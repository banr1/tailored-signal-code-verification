/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChainBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.Send.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.Send.Phase1Placed
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Phase1
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import ProofLib.SepLogic.WP.Apply

/-!
# Budget-Threaded Relocatable Phase 1 Prologue and Epilogues for `spqr::send::<HookRng>` (Block 124)

Verifies the prologue (`+0..+76`) and shared cleanup epilogues (`+4632`, `+4608`, `+904`)
with `VmPreserved`, `FreeOnlyEvs`, and `RustCliAllocBudget` pool transport.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Top.Send.Phase1PlacedBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth hiding Entails.sepExists_elim
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncoderFromPb
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.Unchunked
open CryptoVerification.SpqrV1.States.FromPb
open CryptoVerification.SpqrV1.States.IntoPb
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.Top.DecodeState
open CryptoVerification.SpqrV1.Top.ChainFrom
open CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation
open CryptoVerification.SpqrV1.Top.EncodeVarint
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.Top.Send
  (chainPBAt_entails_first_word chainPBRestAt first_word_entails_chainPBAt
   fsp_add_30_add_30 lsro_spqrSendJumpTablesPlacedAt lsro_spqrSendRoPlacedAt
   lsro_statesFromPbJumpTablePlacedAt lsro_v1StateJumpTablesPlacedAt
   memRegion_7968_split_probes memRegion_rejoin_30_8_8_32 memRegion_rejoin_60_80
   optChainPBAt_none_entails_memRegion_80' probes_entails_memRegion_7968
   seq_clean_lscro sp_sub_3968_add_3872 sp_sub_3968_add_608 sp_sub_4192_sub_3872
   sp_sub_8064_add_4096 sp_sub_8064_add_7968 sp_sub_8064_add_7976 sp_sub_8064_add_7984
   sp_sub_8064_add_7992 sp_sub_8064_add_8000 sp_sub_8064_add_8008 sp_sub_8064_add_8016
   sp_sub_8064_add_8024 sp_sub_8064_add_8032 sp_sub_8064_add_8040 sp_sub_8064_add_8048
   sp_sub_8064_add_8056 sp_sub_96_sub_4096 spqrSendCalleeStack
   spqrSendPlacedEntry spqrSendPlacedProg spqrSendRoSym_bytes_split
   spqrSendSavedRegs spqrSendSavedRegs_eq_sp0
   stackAt_spqrSend_eq_callee_and_frame stackAt_spqrSendCallee_split_allocHook
   stackAt_spqrSendCallee_split_dropStack48 stack_restore_spqrSend)
open CryptoVerification.SpqrV1.Top.Send.Placed
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs
   RustCliAllocBudget VmPreserved rustCliDeallocBudgetSpec rustDeallocEvents)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChainBudget (dropProtoSpqrChainSpec)
open LibsignalBinary.Proofs.SpqrV1.Top.Send.DefsPlacedBudget (AllocContractsPlaced)

export CryptoVerification.SpqrV1.Top.Send
  (seq_clean_lscro spqrSendRoSym_bytes_split lsro_spqrSendJumpTablesPlacedAt
   lsro_statesFromPbJumpTablePlacedAt lsro_v1StateJumpTablesPlacedAt lsro_spqrSendRoPlacedAt)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_sub_592_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_neg592_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_add_688_sub_688
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_96_eq_sp
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm, local wp_norm]
  RustCliAllocBudget.pool_setPC RustCliAllocBudget.pool_advancePC
  RustCliAllocBudget.pool_setPState RustCliAllocBudget.pool_writeReg64
  RustCliAllocBudget.pool_writeReg32 RustCliAllocBudget.pool_writeReg
  RustCliAllocBudget.repAlloc_live
attribute [local simp, local arm64_norm]
  CryptoVerification.SpqrV1.Drop.none2Cap_add_two_beq_zero
  CryptoVerification.SpqrV1.Drop.noneCap_add_two_beq_zero
attribute [local simp, local arm64_norm, local wp_norm]
  CryptoVerification.SpqrV1.Top.Send.sp_sub_96_add_16
  CryptoVerification.SpqrV1.Top.Send.sp_sub_96_add_32
  CryptoVerification.SpqrV1.Top.Send.sp_sub_96_add_48
  CryptoVerification.SpqrV1.Top.Send.sp_sub_96_add_64
  CryptoVerification.SpqrV1.Top.Send.sp_sub_96_add_80
  sp_sub_96_sub_4096 sp_sub_4192_sub_3872 sp_sub_8064_add_4096 sp_sub_3968_add_3872
  sp_sub_8064_add_7968 sp_sub_8064_add_7976 sp_sub_8064_add_7984 sp_sub_8064_add_7992
  sp_sub_8064_add_8000 sp_sub_8064_add_8008 sp_sub_8064_add_8016 sp_sub_8064_add_8024
  sp_sub_8064_add_8032 sp_sub_8064_add_8040 sp_sub_8064_add_8048 sp_sub_8064_add_8056
  sp_sub_3968_add_608 fsp_add_30_add_30

/-! ## `AllocCallPreserved`, `tpidrEl0`, and `deallocFreeOnlySpec` Helpers -/

@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem tpidrEl0_setMem_pre (s : State) (m : Memory) :
    (s.setMem m).tpidrEl0 = s.tpidrEl0 := by cases s; rfl

private theorem acp_refl (s : State) : AllocCallPreserved s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem acp_trans {s₀ s₁ s₂ : State}
    (h01 : AllocCallPreserved s₀ s₁) (h12 : AllocCallPreserved s₁ s₂) :
    AllocCallPreserved s₀ s₂ :=
  ⟨h12.1.trans h01.1, h12.2.1.trans h01.2.1, h12.2.2.1.trans h01.2.2.1,
   h12.2.2.2.1.trans h01.2.2.2.1, h12.2.2.2.2.1.trans h01.2.2.2.2.1,
   h12.2.2.2.2.2.1.trans h01.2.2.2.2.2.1, h12.2.2.2.2.2.2.trans h01.2.2.2.2.2.2⟩

private theorem acp_symm {s₀ s₁ : State} (h : AllocCallPreserved s₀ s₁) :
    AllocCallPreserved s₁ s₀ :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.1.symm, h.2.2.2.1.symm,
   h.2.2.2.2.1.symm, h.2.2.2.2.2.1.symm, h.2.2.2.2.2.2.symm⟩

private theorem acp_right_congr {s s₁ s₂ : State} (h : AllocCallPreserved s₁ s₂) :
    AllocCallPreserved s s₂ ↔ AllocCallPreserved s s₁ :=
  ⟨fun h02 => acp_trans h02 (acp_symm h), fun h01 => acp_trans h01 h⟩

private theorem acp_left_congr {s₁ s₂ sf : State} (h : AllocCallPreserved s₁ s₂) :
    AllocCallPreserved s₂ sf ↔ AllocCallPreserved s₁ sf :=
  ⟨fun h2f => acp_trans h h2f, fun h1f => acp_trans (acp_symm h) h1f⟩

@[local simp, local arm64_norm, local wp_norm]
private theorem acp_refl_iff (s : State) : AllocCallPreserved s s ↔ True :=
  ⟨fun _ => trivial, fun _ => acp_refl s⟩

@[local simp, local arm64_norm, local wp_norm]
private theorem acp_right_setPC (s s' : State) (pc : BitVec 64) :
    AllocCallPreserved s (s'.setPC pc) ↔ AllocCallPreserved s s' :=
  acp_right_congr ⟨by cases s'; rfl, by cases s'; rfl, by cases s'; rfl,
    by cases s'; rfl, by cases s'; rfl, by cases s'; rfl, by cases s'; rfl⟩

@[local simp, local arm64_norm, local wp_norm]
private theorem acp_left_setPC (s' sf : State) (pc : BitVec 64) :
    AllocCallPreserved (s'.setPC pc) sf ↔ AllocCallPreserved s' sf :=
  acp_left_congr ⟨by cases s'; rfl, by cases s'; rfl, by cases s'; rfl,
    by cases s'; rfl, by cases s'; rfl, by cases s'; rfl, by cases s'; rfl⟩

@[local simp, local arm64_norm, local wp_norm]
private theorem acp_right_advancePC (s s' : State) :
    AllocCallPreserved s s'.advancePC ↔ AllocCallPreserved s s' :=
  acp_right_congr ⟨by cases s'; rfl, by cases s'; rfl, by cases s'; rfl,
    by cases s'; rfl, by cases s'; rfl, by cases s'; rfl, by cases s'; rfl⟩

@[local simp, local arm64_norm, local wp_norm]
private theorem acp_left_advancePC (s' sf : State) :
    AllocCallPreserved s'.advancePC sf ↔ AllocCallPreserved s' sf :=
  acp_left_congr ⟨by cases s'; rfl, by cases s'; rfl, by cases s'; rfl,
    by cases s'; rfl, by cases s'; rfl, by cases s'; rfl, by cases s'; rfl⟩

@[local simp, local arm64_norm, local wp_norm]
private theorem acp_right_setPState (s s' : State) (ps : PState) :
    AllocCallPreserved s (s'.setPState ps) ↔ AllocCallPreserved s s' :=
  acp_right_congr ⟨by cases s'; rfl, by cases s'; rfl, by cases s'; rfl,
    by cases s'; rfl, by cases s'; rfl, by cases s'; rfl, by cases s'; rfl⟩

@[local simp, local arm64_norm, local wp_norm]
private theorem acp_left_setPState (s' sf : State) (ps : PState) :
    AllocCallPreserved (s'.setPState ps) sf ↔ AllocCallPreserved s' sf :=
  acp_left_congr ⟨by cases s'; rfl, by cases s'; rfl, by cases s'; rfl,
    by cases s'; rfl, by cases s'; rfl, by cases s'; rfl, by cases s'; rfl⟩

@[local simp, local arm64_norm, local wp_norm]
private theorem acp_right_writeReg64 (s s' : State) (r : Reg) (v : BitVec 64) :
    AllocCallPreserved s (s'.writeReg64 r v) ↔ AllocCallPreserved s s' :=
  acp_right_congr ⟨by cases s'; cases r <;> rfl, by cases s'; cases r <;> rfl,
    by cases s'; cases r <;> rfl, by cases s'; cases r <;> rfl,
    by cases s'; cases r <;> rfl, by cases s'; cases r <;> rfl,
    by cases s'; cases r <;> rfl⟩

@[local simp, local arm64_norm, local wp_norm]
private theorem acp_left_writeReg64 (s' sf : State) (r : Reg) (v : BitVec 64) :
    AllocCallPreserved (s'.writeReg64 r v) sf ↔ AllocCallPreserved s' sf :=
  acp_left_congr ⟨by cases s'; cases r <;> rfl, by cases s'; cases r <;> rfl,
    by cases s'; cases r <;> rfl, by cases s'; cases r <;> rfl,
    by cases s'; cases r <;> rfl, by cases s'; cases r <;> rfl,
    by cases s'; cases r <;> rfl⟩

@[local simp, local arm64_norm, local wp_norm]
private theorem acp_right_writeReg32 (s s' : State) (r : Reg) (v : BitVec 32) :
    AllocCallPreserved s (s'.writeReg32 r v) ↔ AllocCallPreserved s s' :=
  acp_right_writeReg64 s s' r _

@[local simp, local arm64_norm, local wp_norm]
private theorem acp_left_writeReg32 (s' sf : State) (r : Reg) (v : BitVec 32) :
    AllocCallPreserved (s'.writeReg32 r v) sf ↔ AllocCallPreserved s' sf :=
  acp_left_writeReg64 s' sf r _

@[local simp, local arm64_norm, local wp_norm]
private theorem acp_right_writeReg (s s' : State) (w : Width) (r : Reg) (v : BitVec 64) :
    AllocCallPreserved s (s'.writeReg w r v) ↔ AllocCallPreserved s s' :=
  acp_right_writeReg64 s s' r _

@[local simp, local arm64_norm, local wp_norm]
private theorem acp_left_writeReg (s' sf : State) (w : Width) (r : Reg) (v : BitVec 64) :
    AllocCallPreserved (s'.writeReg w r v) sf ↔ AllocCallPreserved s' sf :=
  acp_left_writeReg64 s' sf r _

@[local simp, local arm64_norm, local wp_norm]
private theorem acp_right_applyWriteback (s s' : State) (wb : Option (Reg × BitVec 64)) :
    AllocCallPreserved s (applyWriteback s' wb) ↔ AllocCallPreserved s s' := by
  cases wb with
  | none => rfl
  | some p => exact acp_right_writeReg64 s s' p.1 p.2

@[local simp, local arm64_norm, local wp_norm]
private theorem acp_left_applyWriteback (s' sf : State) (wb : Option (Reg × BitVec 64)) :
    AllocCallPreserved (applyWriteback s' wb) sf ↔ AllocCallPreserved s' sf := by
  cases wb with
  | none => rfl
  | some p => exact acp_left_writeReg64 s' sf p.1 p.2

@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem acp_right_setMem (s s' : State) (m : Memory) :
    AllocCallPreserved s (s'.setMem m) ↔ AllocCallPreserved s s' :=
  acp_right_congr ⟨by cases s'; rfl, by cases s'; rfl, by cases s'; rfl,
    by cases s'; rfl, by cases s'; rfl, by cases s'; rfl, by cases s'; rfl⟩

@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem acp_left_setMem (s' sf : State) (m : Memory) :
    AllocCallPreserved (s'.setMem m) sf ↔ AllocCallPreserved s' sf :=
  acp_left_congr ⟨by cases s'; rfl, by cases s'; rfl, by cases s'; rfl,
    by cases s'; rfl, by cases s'; rfl, by cases s'; rfl, by cases s'; rfl⟩

private theorem align_pre_vm_acp {prog : Program} {target : BitVec 64} {s0 s : State}
    {P P_mid : SepProp} {Q : State → Prop}
    (h : P ⊢ P_mid)
    (hwp : SepWP prog target s P
      (fun sm Pm => sm.tpidrEl0 = s0.tpidrEl0 ∧ AllocCallPreserved s0 sm ∧ (Pm ⊢ P) ∧ Q sm)) :
    SepWP prog target s P
      (fun sm Pm => sm.tpidrEl0 = s0.tpidrEl0 ∧ AllocCallPreserved s0 sm ∧ (Pm ⊢ P_mid) ∧ Q sm) :=
  SepWP.mono hwp fun _ _ _ _ ⟨htp, hacp, hPm, hQ⟩ => ⟨htp, hacp, Entails.trans hPm h, hQ⟩

private theorem align_done_st {prog : Program} {target : BitVec 64} {s_cur : State}
    {P_cur : SepProp} {P_mid : State → SepProp} {Q : State → Prop}
    (hent : P_cur ⊢ P_mid s_cur)
    (hwp : SepWP prog target s_cur P_cur (fun sm Pm => (Pm ⊢ P_cur) ∧ sm = s_cur ∧ Q sm)) :
    SepWP prog target s_cur P_cur (fun sm Pm => (Pm ⊢ P_mid sm) ∧ Q sm) :=
  SepWP.mono hwp fun _ _ _ _ ⟨hPm, rfl, hQ⟩ => ⟨Entails.trans hPm hent, hQ⟩

private theorem sepWP_intro_evs {prog : Program} {target : BitVec 64} {s_cur : State}
    {P_cur : SepProp} (evs : List AllocEvent) (hfo : FreeOnlyEvs evs)
    {R : List AllocEvent → State → SepProp → Prop}
    (hwp : SepWP prog target s_cur P_cur (R evs)) :
    SepWP prog target s_cur P_cur (fun sm Pm => ∃ evs', FreeOnlyEvs evs' ∧ R evs' sm Pm) :=
  SepWP.mono hwp fun _ _ _ _ h => ⟨evs, hfo, h⟩

private def deallocFreeOnlySpec [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (BitVec 64 × Nat × Nat × M.σ) where
  pre := (rustCliDeallocBudgetSpec M A lim).pre
  post := fun (_, size, align, st) s0 sf =>
    ⌜sf.trace = s0.trace ∧ AllocCallPreserved s0 sf⌝ ∗
      A.pool lim (M.stepEvents (rustDeallocEvents size align) st) sf ∗ stackAt s0.sp allocHookStack

private theorem subroutine_ok_deallocFreeOnly [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok prog entry (deallocFreeOnlySpec M A lim) := by
  refine subroutine_ok_mono h (fun _ _ _ hp => hp) (fun _ _ _ _ hq => ?_)
  dsimp only [rustCliDeallocBudgetSpec, deallocFreeOnlySpec] at hq ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
  exact ⟨⟨hq.1.1.2.1, hq.1.1⟩, hq.2⟩

variable [LibsignalPlacement]

/-! ## Shared Epilogue (`+4632 -> s0.lr`) -/

/-- Relocatable epilogue (`+4632 -> s0.lr`) with `VmPreserved` and `AllocCallPreserved`:
    adds `0x1000 + 0xf20 = 0x1f20` (`7968`) to `sp = s0.sp - 0x1f80`, restores `x19..x30`
    from `s0.sp - 96`, and executes `ret`. -/
theorem spqr_send_epilogue_4632_placed {ext : String → Option (State → State)}
    (s0 s : State) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = spqrSendPlacedEntry + 4632#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 0x1f80#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0 := by simp only [wp_norm, arm64_norm, *]) :
    SepWP (spqrSendPlacedProg ext) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
        memRegion (s0.sp - 0x1f80#64) 0x1f20 ∗
        spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗ Rest)
      (fun sf Pf =>
        VmPreserved s sf ∧
        AllocCallPreserved s sf ∧
        (Pf ⊢ stackAt s0.sp spqrSendStack ∗ Rest) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s.trace) := by
  have hfsp_align : ((s0.sp - 0x1f80#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 0x1f80#64 hsp0_align (by decide)
  have hsp96_align : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 96#64 hsp0_align (by decide)
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc ⊢
  rw [spqrSendSavedRegs_eq_sp0 s0]
  by_vm_steps (
    wp_steps
    refine align_pre_vm_acp ?_ ?_
    · have hrest := stack_restore_spqrSend s0.sp s0
      rw [spqrSendSavedRegs_eq_sp0 s0] at hrest
      refine Entails.trans
        (Entails.of_eq (show _ =
          (stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
           memRegion (s0.sp - 0x1f80#64) 0x1f20 ∗
           (((s0.sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗
            ((s0.sp - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
            ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x28) ∗
            ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
            ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗
            ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
            ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗
            ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
            ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
            ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
            ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
            ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) ∗ Rest by ac_rfl))
        (sepConj_mono_left hrest)
    · wp_done)

theorem spqr_send_epilogue_4632_pool_placed {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : String → Option (State → State)}
    (s0 s : State) (st : M.σ) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = spqrSendPlacedEntry + 4632#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 0x1f80#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0 := by simp only [wp_norm, arm64_norm, *]) :
    SepWP (spqrSendPlacedProg ext) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
        memRegion (s0.sp - 0x1f80#64) 0x1f20 ∗
        spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
        A.pool lim st s ∗ Rest)
      (fun sf Pf =>
        VmPreserved s sf ∧
        AllocCallPreserved s sf ∧
        (Pf ⊢ stackAt s0.sp spqrSendStack ∗ A.pool lim st sf ∗ Rest) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s.trace) := by
  have hep := spqr_send_epilogue_4632_placed (ext := ext) s0 s (A.pool lim st s ∗ Rest)
    hsp0_align hpc hrun hsp hvregs
  refine SepWP.mono hep ?_
  intro sf Pf _ _ ⟨hvm, hacp, hPf, hsp_f, hcc_f, htr_f⟩
  refine ⟨hvm, hacp, ?_, hsp_f, hcc_f, htr_f⟩
  rw [A.pool_transport lim st s sf hvm]
  exact Entails.trans hPf (Entails.of_eq (by ac_rfl))

/-! ## Prologue (`+0 -> +76`) -/

/-- Relocatable prologue (`+0 -> +76`) with `VmPreserved` and `AllocCallPreserved`:
    saves `x19..x30` at `s0.sp - 96`, sets `x29 = s0.sp - 96`, `sp = s0.sp - 0x1f80`,
    `x19 = ret`, `x0 = stV`, `x8 = x21 = x26 = sp + 0x1260`, and probes `[s0.sp - 4192]` and `[sp]`. -/
theorem spqr_send_prologue_placed {ext : String → Option (State → State)}
    (s0 : State) (ret stV : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s0.pc = spqrSendPlacedEntry)
    (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = ret)
    (hx1 : s0.readReg64 .x1 = stV) :
    SepWP (spqrSendPlacedProg ext)
      (spqrSendPlacedEntry + 76#64) s0
      (stackAt s0.sp spqrSendStack ∗ Rest)
      (fun s1 P1 =>
        VmPreserved s0 s1 ∧
        AllocCallPreserved s0 s1 ∧
        (P1 ⊢
          stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
          memRegion (s0.sp - 0x1f80#64) 0x1f20 ∗
          spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗ Rest) ∧
        s1.sp = s0.sp - 0x1f80#64 ∧
        s1.readReg64 .x29 = s0.sp - 96#64 ∧
        s1.readReg64 .x19 = ret ∧
        s1.readReg64 .x0 = stV ∧
        s1.readReg64 .x8 = (s0.sp - 0x1f80#64) + 0x1260#64 ∧
        s1.readReg64 .x21 = (s0.sp - 0x1f80#64) + 0x1260#64 ∧
        s1.readReg64 .x26 = (s0.sp - 0x1f80#64) + 0x1260#64 ∧
        s1.trace = s0.trace ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s0) := by
  have hfsp_align : ((s0.sp - 0x1f80#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 0x1f80#64 hsp0_align (by decide)
  have hsp4192_align : ((s0.sp - 4192#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 4192#64 hsp0_align (by decide)
  have hsp96_align : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 96#64 hsp0_align (by decide)
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc ⊢
  by_vm_steps (
    wp_conv_pre =>
      rw [stackAt_spqrSend_eq_callee_and_frame s0.sp,
          sp_sub_8064_add_7968 s0.sp,
          ProofLib.memRegion_cells (s0.sp - 96#64) 12 (by decide),
          memRegion_7968_split_probes s0.sp]
    cells_unfold
    wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply ProofLib.SepWP.exists_left; intro w0
    apply ProofLib.SepWP.exists_left; intro w1
    apply ProofLib.SepWP.exists_left; intro w2
    apply ProofLib.SepWP.exists_left; intro w3
    apply ProofLib.SepWP.exists_left; intro w4
    apply ProofLib.SepWP.exists_left; intro w5
    apply ProofLib.SepWP.exists_left; intro w6
    apply ProofLib.SepWP.exists_left; intro w7
    apply ProofLib.SepWP.exists_left; intro w8
    apply ProofLib.SepWP.exists_left; intro w9
    apply ProofLib.SepWP.exists_left; intro w10
    apply ProofLib.SepWP.exists_left; intro w11
    apply ProofLib.SepWP.exists_left; intro v_probe
    apply ProofLib.SepWP.exists_left; intro v0
    wp_steps
    refine align_pre_vm_acp ?_ ?_
    · rw [spqrSendSavedRegs_eq_sp0 s0]
      have hfsp := probes_entails_memRegion_7968 s0.sp 0#64 0#64
      refine Entails.trans
        (Entails.of_eq (show _ =
          (((s0.sp - 0x1f80#64) ↦₆₄ 0#64) ∗
           memRegion (s0.sp - 8056#64) 3864 ∗
           ((s0.sp - 4192#64) ↦₆₄ 0#64) ∗
           memRegion (s0.sp - 4184#64) 4088) ∗
          (stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
           (((s0.sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗
            ((s0.sp - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
            ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x28) ∗
            ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
            ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗
            ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
            ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗
            ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
            ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
            ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
            ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
            ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)) ∗
           Rest) by ac_rfl))
        (Entails.trans (sepConj_mono_left hfsp) (Entails.of_eq (by ac_rfl)))
    · wp_done)

theorem spqr_send_prologue_pool_placed {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : String → Option (State → State)}
    (s0 : State) (st : M.σ) (ret stV : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s0.pc = spqrSendPlacedEntry)
    (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = ret)
    (hx1 : s0.readReg64 .x1 = stV) :
    SepWP (spqrSendPlacedProg ext)
      (spqrSendPlacedEntry + 76#64) s0
      (stackAt s0.sp spqrSendStack ∗ A.pool lim st s0 ∗ Rest)
      (fun s1 P1 =>
        VmPreserved s0 s1 ∧
        AllocCallPreserved s0 s1 ∧
        (P1 ⊢
          stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
          memRegion (s0.sp - 0x1f80#64) 0x1f20 ∗
          spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
          A.pool lim st s1 ∗ Rest) ∧
        s1.sp = s0.sp - 0x1f80#64 ∧
        s1.readReg64 .x29 = s0.sp - 96#64 ∧
        s1.readReg64 .x19 = ret ∧
        s1.readReg64 .x0 = stV ∧
        s1.readReg64 .x8 = (s0.sp - 0x1f80#64) + 0x1260#64 ∧
        s1.readReg64 .x21 = (s0.sp - 0x1f80#64) + 0x1260#64 ∧
        s1.readReg64 .x26 = (s0.sp - 0x1f80#64) + 0x1260#64 ∧
        s1.trace = s0.trace ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s0) := by
  have hpr := spqr_send_prologue_placed (ext := ext) s0 ret stV (A.pool lim st s0 ∗ Rest)
    hsp0_align hpc hrun hx0 hx1
  refine SepWP.mono hpr ?_
  intro s1 P1 _ _ ⟨hvm, hacp, hP1, hsp1, hx29, hx19, hx0', hx8, hx21, hx26, htr1, hvregs1⟩
  refine ⟨hvm, hacp, ?_, hsp1, hx29, hx19, hx0', hx8, hx21, hx26, htr1, hvregs1⟩
  rw [A.pool_transport lim st s0 s1 hvm]
  exact Entails.trans hP1 (Entails.of_eq (by ac_rfl))

/-! ## Budget-Threaded Shared Cleanup Epilogues (`+4608` and `+904`) -/

/-- Budget-threaded relocatable shared `st.chain` drop + register-restore epilogue (`+4608 -> s0.lr`):
    drops `ProtoRepr.optChainPBAt A.repAlloc ((s0.sp - 0x1f80#64) + 0x60#64) optCh` (calling Block
    `136` when `some`), rejoins `memRegion (s0.sp - 0x1f80#64) 0x1f20`, and runs
    `spqr_send_epilogue_4632_pool_placed`. -/
theorem spqr_send_chain_drop_epilogue_4608_placed {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdrop : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 136)
      (withLsCodeRoLoaded lsmpl (dropProtoSpqrChainSpec M A lim)))
    (s0 s : State) (st : M.σ) (optCh : Option ChainPB) (Rest : SepProp)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = spqrSendPlacedEntry + 4608#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 0x1f80#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0 := by simp only [wp_norm, arm64_norm, *]) :
    SepWP (spqrSendPlacedProg ext) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
        memRegion (s0.sp - 0x1f80#64) 0x60 ∗
        optChainPBAt A.repAlloc ((s0.sp - 0x1f80#64) + 0x60#64) optCh ∗
        memRegion ((s0.sp - 0x1f80#64) + 0xb0#64) (0x1f20 - 0xb0) ∗
        spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
        A.pool lim st s ∗ Rest)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          AllocCallPreserved s sf ∧
          (Pf ⊢ stackAt s0.sp spqrSendStack ∗ A.pool lim (M.stepEvents evs st) sf ∗ Rest) ∧
          sf.sp = s0.sp ∧
          CalleeSavedPreserved s0 sf ∧
          sf.trace = s.trace) := by
  have hfsp_align : ((s0.sp - 0x1f80#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 0x1f80#64 hsp0_align (by decide)
  refine SepWP.seq
    (mid := spqrSendPlacedEntry + 4632#64)
    (Mid := fun sm Pm =>
      ∃ evs : List AllocEvent,
        FreeOnlyEvs evs ∧
        (Pm ⊢
          stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
          memRegion (s0.sp - 0x1f80#64) 0x1f20 ∗
          spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
          A.pool lim (M.stepEvents evs st) sm ∗ Rest) ∧
        AllocCallPreserved s sm ∧
        sm.sp = s0.sp - 0x1f80#64 ∧
        sm.trace = s.trace ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0)
    ?_ ?_
  · dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry,
      withLsCodeRoLoaded, LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChainBudget.dropProtoSpqrChainSpec,
      chainPBSize, BitVec.ofNat_eq_ofNat] at hpc hdrop ⊢
    generalize hfsp_eq : s0.sp - 8064#64 = fsp at hsp hfsp_align ⊢
    cases optCh with
    | none =>
      have hnone : optChainPBAt A.repAlloc (fsp + 96#64) none =
          (((fsp + 96#64) ↦₆₄ LibsignalTripleRatchetRepr.noneCap) ∗
           memRegion ((fsp + 96#64) + 8#64) 72) := rfl
      wp_conv_pre => rw [hnone]
      wp_steps
      refine sepWP_intro_evs [] FreeOnlyEvs.nil ?_
      refine align_done_st ?_ ?_
      · simp only [AllocCostModel.stepEvents_nil, RustCliAllocBudget.pool_setPC,
          RustCliAllocBudget.pool_advancePC, RustCliAllocBudget.pool_setPState,
          RustCliAllocBudget.pool_writeReg64, RustCliAllocBudget.pool_writeReg32,
          RustCliAllocBudget.pool_writeReg]
        have hch := optChainPBAt_none_entails_memRegion_80' A.repAlloc (fsp + 96#64)
        rw [hnone] at hch
        refine Entails.trans
          (Entails.of_eq (show _ =
            ((fsp + 96#64) ↦₆₄ LibsignalTripleRatchetRepr.noneCap ∗
             memRegion ((fsp + 96#64) + 8#64) 72) ∗
            (memRegion fsp 96 ∗
             memRegion (fsp + 176#64) 7792 ∗
             stackAt fsp spqrSendCalleeStack ∗
             spqrSendSavedRegs fsp s0 ∗
             A.pool lim st s ∗ Rest) by ac_rfl)) ?_
        refine Entails.trans (sepConj_mono_left hch) ?_
        rw [← memRegion_rejoin_60_80 fsp]
        exact Entails.of_eq (by ac_rfl)
      · wp_done
    | some ch =>
      have hsome : optChainPBAt A.repAlloc (fsp + 96#64) (some ch) =
          chainPBAt A.repAlloc (fsp + 96#64) ch := rfl
      wp_conv_pre => rw [hsome]
      refine SepWP.weaken_pre
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
          (chainPBAt_entails_first_word A.repAlloc (fsp + 96#64) ch)))) ?_
      wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      apply ProofLib.SepWP.exists_left; intro cap
      apply ProofLib.SepWP.exists_left; intro ptr
      wp_focus_pure; intro hcap_lt
      have hne_none := CryptoVerification.SpqrV1.Drop.cap_add_one_beq_zero_false hcap_lt
      wp_steps
      refine SepWP.weaken_pre
        (Entails.trans
          (Entails.of_eq (show _ =
            ((fsp + 96#64) ↦₆₄ cap ∗
             chainPBRestAt A.repAlloc (fsp + 96#64) cap ptr ch) ∗
            (stackAt fsp spqrSendCalleeStack ∗
             memRegion fsp 96 ∗
             memRegion (fsp + 176#64) 7792 ∗
             spqrSendSavedRegs fsp s0 ∗
             A.pool lim st s ∗ Rest) by ac_rfl))
          (sepConj_mono_left (first_word_entails_chainPBAt A.repAlloc (fsp + 96#64) cap ptr ch))) ?_
      wp_conv_pre => rw [stackAt_spqrSendCallee_split_dropStack48 fsp]
      have hcl : LibsignalCodeLoaded lsmpl s.mem := hcrl.1
      have hro : LibsignalRoLoaded lsmpl s.mem := hcrl.2
      wp_call hdrop (⟨fsp + 96#64, ch⟩, st)
      simp only [acp_left_setPC, acp_left_advancePC, acp_left_setPState,
        acp_left_writeReg64, acp_left_writeReg32, acp_left_writeReg,
        acp_left_applyWriteback] at *
      have hacp_sf : AllocCallPreserved s sf := by assumption
      rcases hacp_sf with ⟨_, _, _, _, _, _, _⟩
      have hfo_w : FreeOnlyEvs w := by assumption
      refine sepWP_intro_evs w hfo_w ?_
      refine align_done_st ?_ ?_
      · rw [hsp, stackAt_spqrSendCallee_split_dropStack48 fsp, ← memRegion_rejoin_60_80 fsp]
        exact Entails.of_eq (by ac_rfl)
      · wp_done
  · intro s2 P2 hpc2 hrun2 ⟨evs, hfo, hP2, hacp1, hsp2, htr2, hvregs2⟩
    refine SepWP.weaken_pre hP2 ?_
    have hep := spqr_send_epilogue_4632_pool_placed (A := A) (lim := lim) (ext := ext)
      s0 s2 (M.stepEvents evs st) Rest hsp0_align hpc2 hrun2 hsp2 hvregs2
    refine SepWP.mono hep ?_
    intro sf Pf _ _ ⟨_, hacp2, hPf, hsp_f, hcc_f, htr_f⟩
    exact ⟨evs, hfo, acp_trans hacp1 hacp2, hPf, hsp_f, hcc_f, htr_f.trans htr2⟩

/-- Budget-threaded relocatable shared `st.version_negotiation.auth_key` dealloc + `st.chain` drop +
    register-restore epilogue (`+904 -> s0.lr`):
    loads `w1` from `[sp + 0x38]`, calls `__rust_dealloc(w1, w0.toNat, 1)`, and jumps to `+4608`. -/
theorem spqr_send_vn_chain_drop_epilogue_904_placed {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced M A lim ext)
    (hdrop : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 136)
      (withLsCodeRoLoaded lsmpl (dropProtoSpqrChainSpec M A lim)))
    (s0 s : State) (st : M.σ) (w0 w1 : BitVec 64) (optCh : Option ChainPB) (Rest : SepProp)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = spqrSendPlacedEntry + 904#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 0x1f80#64)
    (hx23 : s.readReg64 .x23 = w0)
    (hw0_pos : 0 < w0.toNat)
    (hw0_lt : w0.toNat < 2 ^ 63)
    (hw1_ne : w1 ≠ 0)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0 := by simp only [wp_norm, arm64_norm, *]) :
    SepWP (spqrSendPlacedProg ext) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
        memRegion (s0.sp - 0x1f80#64) 0x30 ∗
        memRegion ((s0.sp - 0x1f80#64) + 0x30#64) 8 ∗
        (((s0.sp - 0x1f80#64) + 0x38#64) ↦₆₄ w1) ∗
        memRegion ((s0.sp - 0x1f80#64) + 0x40#64) 32 ∗
        A.live w1 w0.toNat 1 ∗
        memRegion w1 w0.toNat ∗
        optChainPBAt A.repAlloc ((s0.sp - 0x1f80#64) + 0x60#64) optCh ∗
        memRegion ((s0.sp - 0x1f80#64) + 0xb0#64) (0x1f20 - 0xb0) ∗
        spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
        A.pool lim st s ∗ Rest)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          AllocCallPreserved s sf ∧
          (Pf ⊢ stackAt s0.sp spqrSendStack ∗ A.pool lim (M.stepEvents evs st) sf ∗ Rest) ∧
          sf.sp = s0.sp ∧
          CalleeSavedPreserved s0 sf ∧
          sf.trace = s.trace) := by
  have hfsp_align : ((s0.sp - 0x1f80#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 0x1f80#64 hsp0_align (by decide)
  have hdealloc_fo : subroutine_ok (spqrSendPlacedProg ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (deallocFreeOnlySpec M A lim) :=
    subroutine_ok_deallocFreeOnly (spqr_hook_ok_of_mem hA.dealloc)
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  have hstep : SepWP (spqrSendPlacedProg ext) (spqrSendPlacedEntry + 4608#64) s
      (stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
        memRegion (s0.sp - 0x1f80#64) 0x30 ∗
        memRegion ((s0.sp - 0x1f80#64) + 0x30#64) 8 ∗
        (((s0.sp - 0x1f80#64) + 0x38#64) ↦₆₄ w1) ∗
        memRegion ((s0.sp - 0x1f80#64) + 0x40#64) 32 ∗
        A.live w1 w0.toNat 1 ∗
        memRegion w1 w0.toNat ∗
        optChainPBAt A.repAlloc ((s0.sp - 0x1f80#64) + 0x60#64) optCh ∗
        memRegion ((s0.sp - 0x1f80#64) + 0xb0#64) (0x1f20 - 0xb0) ∗
        spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
        A.pool lim st s ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢
          stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
          memRegion (s0.sp - 0x1f80#64) 0x60 ∗
          optChainPBAt A.repAlloc ((s0.sp - 0x1f80#64) + 0x60#64) optCh ∗
          memRegion ((s0.sp - 0x1f80#64) + 0xb0#64) (0x1f20 - 0xb0) ∗
          spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
          A.pool lim (M.stepEvents (rustDeallocEvents w0.toNat 1) st) sm ∗ Rest) ∧
        AllocCallPreserved s sm ∧
        sm.sp = s0.sp - 0x1f80#64 ∧
        sm.trace = s.trace ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0) := by
    dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc hdealloc_fo ⊢
    generalize hfsp_eq : s0.sp - 8064#64 = fsp at hsp hfsp_align ⊢
    wp_steps
    wp_conv_pre => rw [stackAt_spqrSendCallee_split_allocHook fsp]
    wp_call hdealloc_fo (w1, w0.toNat, 1, st)
    simp only [acp_left_setPC, acp_left_advancePC, acp_left_setPState,
      acp_left_writeReg64, acp_left_writeReg32, acp_left_writeReg,
      acp_left_applyWriteback] at *
    have hacp_sf : AllocCallPreserved s sf := by assumption
    rcases hacp_sf with ⟨_, _, _, _, _, _, _⟩
    wp_steps
    refine align_done_st ?_ ?_
    · simp only [RustCliAllocBudget.pool_setPC, RustCliAllocBudget.pool_advancePC,
        RustCliAllocBudget.pool_setPState, RustCliAllocBudget.pool_writeReg64,
        RustCliAllocBudget.pool_writeReg32, RustCliAllocBudget.pool_writeReg]
      rw [hsp, stackAt_spqrSendCallee_split_allocHook fsp]
      have h60 := memRegion_rejoin_30_8_8_32 fsp w1
      refine Entails.trans
        (Entails.of_eq (show _ =
          (memRegion fsp 48 ∗
           memRegion (fsp + 48#64) 8 ∗
           ((fsp + 56#64) ↦₆₄ w1) ∗
           memRegion (fsp + 64#64) 32) ∗
          (memRegion (fsp - 123008#64) (spqrSendCalleeStack - allocHookStack) ∗
           stackAt fsp allocHookStack ∗
           optChainPBAt A.repAlloc (fsp + 96#64) optCh ∗
           memRegion (fsp + 176#64) 7792 ∗
           spqrSendSavedRegs fsp s0 ∗
           A.pool lim (M.stepEvents (rustDeallocEvents w0.toNat 1) st) sf ∗ Rest) by ac_rfl)) ?_
      refine Entails.trans (sepConj_mono_left h60) ?_
      exact Entails.of_eq (by ac_rfl)
    · wp_done
  refine sepWP_seq_lscro hcrl (SepWP.mono hstep ?_)
  intro s2 P2 hpc2 hrun2 ⟨hP2, hacp1, hsp2, htr2, hvregs2⟩ hcrl2
  refine SepWP.weaken_pre hP2 ?_
  have hep := spqr_send_chain_drop_epilogue_4608_placed hdrop s0 s2
    (M.stepEvents (rustDeallocEvents w0.toNat 1) st) optCh Rest
    hcrl2 hsp0_align hpc2 hrun2 hsp2 hvregs2
  refine SepWP.mono hep ?_
  intro sf Pf _ _ ⟨evs₂, hfo₂, hacp2, hPf, hsp_f, hcc_f, htr_f⟩
  refine ⟨rustDeallocEvents w0.toNat 1 ++ evs₂,
    (FreeOnlyEvs.singleton 1 w0.toNat).append hfo₂,
    acp_trans hacp1 hacp2, ?_, hsp_f, hcc_f, htr_f.trans htr2⟩
  rw [M.stepEvents_append]
  exact hPf

end LibsignalBinary.Proofs.SpqrV1.Top.Send.Phase1PlacedBudget
