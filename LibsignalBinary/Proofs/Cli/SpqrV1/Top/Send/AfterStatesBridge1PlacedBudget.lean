/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Cli.SpqrV1.Drop.States1aPlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesBridge1Placed
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesBridge1PlacedBudgetAux
public import LibsignalBinary.Proofs.Common.SharedHelpers
public import LibsignalBinary.Proofs.SpqrV1.Chain.AddEpochHelpersBudget
public import LibsignalBinary.Proofs.SpqrV1.Chain.IntoPbHelpersBudget
public import LibsignalBinary.Proofs.SpqrV1.Chain.SendKeyHelpersBudget
public import LibsignalBinary.Proofs.SpqrV1.Drop.ChainEpochBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.ChainFrom.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.ChainFromVersionNegotiation.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesBridge1
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesChainResolvePlacedBudget
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice

/-!
# Budget-Threaded `spqr::send` Phase 3b–3c Bridge (`+3196..+4000` and Error Epilogue)

Threads `RustCliAllocBudget` through the `[LibsignalPlacement]` Phase 3b–3c chain resolution
composition and `+4576..+4664` epilogue of `spqr::send::<signal_session_ratchet::Coins>`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesBridge1PlacedBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement libsignalSessionCode lsmpl lsρ sepWP_seq_lscl
   withLsCodeLoaded)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.LibsignalTripleRatchet
  (LibsignalCodeRoLoaded spqrSendResultAt spqrSendStack withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.LibsignalSpqrV1
  (Bytes Chain ChainPB Epoch EpochSecret Error HkdfFn SpqrApiResult States Version
   VersionNegotiationPB chainFromVersionNegotiation spqrAuthApi spqrPolyApi)
open CryptoVerification.SpqrV1.ProtoRepr (optChainPBAt optVersionNegotiationPBAt)
open CryptoVerification.SpqrV1.ProtoRepr renaming chainPBAt → protoChainPBAt
open CryptoVerification.SpqrV1.Drop (chunkedStatesAt)
open CryptoVerification.SpqrV1.ChainProofs
  (ChainAddEpochGhost ChainIntoPbCall ChainSendKeyGhost chainAddEpochStackX chainAt chainEpochSize
   chainIntoPbStackX chainRepr chainSendKeyStackX epochSecretAt sendKeyErrAt sendKeyPostAt)
open CryptoVerification.SpqrV1.Top.DecodeState (vecU8Heap)
open CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation
  (ChainFromVersionNegotiationCall chainErrorAt chainFromVersionNegotiationStackX chainResultAt
   versionNegotiationPBAt)
open CryptoVerification.SpqrV1.Top.ChainFrom (ChainFromPbCall chainFromPbStackX chainPBAt)
open CryptoVerification.SpqrV1.Top.StateSize (optRaw rawChain)
open CryptoVerification.Cli.SpqrV1.Drop (chunkedStatesLocal1JumpTablePlacedAt)
open CryptoVerification.Cli.SpqrV1.Top.Send
  (call_lscro_calleeStack_anyPanic corePanic_spqrSend_placed_extern of_sepWP_lscro_b1
   panicSubOverflow_spqrSend_placed_extern panic_lscro_calleeStack_anyPanic
   sendChainTargetPCPlaced spqrSendPlacedEntry spqrSendPlacedProg)
open CryptoVerification.SpqrV1.Top.Send
  (chainAt_entails_links_grow_ok chainOrigSlotAt chainOrigSlotAt_none
   chain_links_length_le_rawChain optChainPBRegSlotAt optEpochSecretRegSlotAt
   pure_elim_focus_b1 sendChainPhase sendKeyIntoPbChain sendResolveChain
   sendResolveChain_raw_le sendStepChain sepWPp_at_panic_stub spqrSendCalleeStack
   spqrSendSavedRegs vn_some_pack)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget
   SeqEnv VmPreserved rustAllocEvents)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624 lsRetAddr624_base_add)
open LibsignalBinary.Proofs.Cli.SpqrV1.Drop.States1aPlacedBudget (dropChunkedStatesLocal1PlacedSpec)
open LibsignalBinary.Proofs.SpqrV1.Drop.ChainEpochBudget (dropChainEpochSliceSpec)
open LibsignalBinary.Proofs.SpqrV1.Chain.AddEpochHelpersBudget
  (ChainAddEpochEnv chainAddEpochEvents chainAddEpochSpecX)
open LibsignalBinary.Proofs.SpqrV1.Chain.SendKeyHelpersBudget (ChainSendKeyAllocEnv chainSendKeySpecX)
open LibsignalBinary.Proofs.SpqrV1.Chain.IntoPbHelpersBudget
  (ChainIntoPbAllocEnv ChainIntoPbEnv chainIntoPbSpecX fitsEnv_chainIntoPbAllocEnv_of_chainIntoPbEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.ChainFrom.DefsBudget (ChainFromVersionNegotiationEnv chainFromPbSpecX)
open LibsignalBinary.Proofs.SpqrV1.Top.ChainFromVersionNegotiation.DefsBudget (chainFromVersionNegotiationSpecX)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesChainPlacedBudget
  (DeallocOkPlaced step_drop_key_31784_placed step_epilogue_31a3c_placed
   step_epilogue_31a54_placed step_epilogue_31a74_placed step_err_31764_placed
   step_err_31794_placed step_panic_33740_placed step_panic_33d4c_placed)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesChainResolvePlacedBudget
  (step_branch_chain_none_314d8_placed step_from_vn_le_zero_3164c_placed
   step_min_version_zero_ok_317d8_placed step_post_from_pb_ok_31510_placed
   step_post_from_vn_ok_31674_placed step_pre_from_pb_314d8_placed
   step_pre_from_vn_3164c_placed)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesBridge1PlacedBudgetAux
  (SendChainPhaseEnv SendStepChainEnv addsPState64_noneCap_z
   addsPState64_z_false_of_ne_noneCap call_lscro_calleeStack_evs_anyPanic
   dropChunkedStatesLocal1PlacedSpec_eq flag_of_csinc_315b8
   memRegion_1060_80_eq_24_56 memRegion_590_88_eq_24_64 memRegion_590_88_eq_80_8
   sendChainPostPlaced sendChainPostPlaced_mono sendChainPostPlaced_step
   sepWPp_mono_post setPC_preserves step_chain_5b8_to_7fc_placed
   step_from_pb_err_31510_to_31a3c_placed step_from_vn_err_31674_to_31a3c_placed
   step_panic_key_without_chain_317d8_placed step_vn_none_3164c_to_31a3c_placed)

export LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesBridge1PlacedBudgetAux
  (SendChainPhaseEnv SendStepChainEnv call_lscro_calleeStack_evs_anyPanic
   dropChunkedStatesLocal1PlacedSpec_eq sendChainPostPlaced)

variable [LibsignalPlacement]

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnAddr Program.fnOff Obj.lookup

/-! ## 1. Epilogue (`+4600`, `+4576`) -/

theorem step_epilogue_from_31a54_placed {ext : String → Option (State → State)}
    (s0 s : State) (x23 : BitVec 64) (Frame : SepProp)
    (hpc : s.pc = spqrSendPlacedEntry + 4600#64) (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 0x1f80#64)
    (hx23 : s.readReg64 .x23 = x23) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0 := by simp only [wp_norm, arm64_norm, *]) :
    SepWP (spqrSendPlacedProg ext) (s0.readReg64 .x30) s
      (memRegion s.sp 0x60 ∗ chainOrigSlotAt s.sp x23 ∗ memRegion (s.sp + 0xb0#64) (0x1f20 - 0xb0) ∗
        stackAt s.sp spqrSendCalleeStack ∗ spqrSendSavedRegs s.sp s0 ∗ Frame)
      (fun sf Q => VmPreserved s sf ∧ sf.status = .Running ∧ sf.trace = s.trace ∧ sf.sp = s0.sp ∧
        Arm64.CalleeSavedPreserved s0 sf ∧ (Q ⊢ stackAt s0.sp spqrSendStack ∗ Frame)) := by
  have hsp_align : (s.sp &&& 15#64 == 0#64) = true := by
    rw [hsp]; exact spAligned_sub s0.sp 0x1f80#64 hsp0_align (by decide)
  have hstep1 := step_epilogue_31a54_placed (ext := ext) s x23
    (memRegion s.sp 0x60 ∗ memRegion (s.sp + 0xb0#64) (0x1f20 - 0xb0) ∗
      stackAt s.sp spqrSendCalleeStack ∗ spqrSendSavedRegs s.sp s0 ∗ Frame) hpc hrun hx23 hsp_align
  refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) (SepWP.seq hstep1 ?_)
  intro s1 P1 hpc1 _ ⟨hvm1, hrun1, htr1, hsp1, hvregs1, hP1⟩
  have hjoin : memRegion (s.sp + 0x60#64) 80 ∗
      (memRegion s.sp 0x60 ∗ memRegion (s.sp + 0xb0#64) (0x1f20 - 0xb0) ∗
        stackAt s.sp spqrSendCalleeStack ∗ spqrSendSavedRegs s.sp s0 ∗ Frame) ⊢
      stackAt s1.sp spqrSendCalleeStack ∗ memRegion s1.sp 0x1f20 ∗ spqrSendSavedRegs s1.sp s0 ∗ Frame := by
    rw [hsp1,
      ProofLib.memRegion_split' (b := s.sp) (n := 0x60) (k := 0x1f20 - 0x60) (b' := s.sp + 0x60#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := s.sp + 0x60#64) (n := 80) (k := 0x1f20 - 0xb0) (b' := s.sp + 0xb0#64) rfl (by bv_omega) (by decide)]
    exact Entails.of_eq (by sep_ac_rfl)
  refine SepWP.weaken_pre (Entails.trans hP1 hjoin)
    (SepWP.mono (step_epilogue_31a74_placed s0 s1 Frame hpc1 hrun1 (hsp1.trans hsp) hsp0_align (hvregs1.trans hvregs)) ?_)
  intro sf Q _ _ ⟨hvmf, hrunf, htrf, hspf, hcsf, hQ⟩
  exact ⟨hvm1.trans hvmf, hrunf, htrf.trans htr1, hspf, hcsf, hQ⟩

theorem step_epilogue_from_31a3c_placed {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ext : String → Option (State → State)} (hdealloc : DeallocOkPlaced M A lim ext)
    (s0 s : State) (st : M.σ) (vn : Option VersionNegotiationPB) (x23 : BitVec 64) (Frame : SepProp)
    (hpc : s.pc = spqrSendPlacedEntry + 4576#64) (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 0x1f80#64)
    (hx23 : s.readReg64 .x23 = x23) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0 := by simp only [wp_norm, arm64_norm, *]) :
    SepWP (spqrSendPlacedProg ext) (s0.readReg64 .x30) s
      (memRegion s.sp 0x30 ∗ optVersionNegotiationPBAt A.repAlloc (s.sp + 0x30#64) vn ∗
        chainOrigSlotAt s.sp x23 ∗ memRegion (s.sp + 0xb0#64) (0x1f20 - 0xb0) ∗
        A.pool lim st s ∗ stackAt s.sp spqrSendCalleeStack ∗ spqrSendSavedRegs s.sp s0 ∗ Frame)
      (fun sf Q => ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
        sf.status = .Running ∧ sf.trace = s.trace ∧ sf.sp = s0.sp ∧ Arm64.CalleeSavedPreserved s0 sf ∧
        (Q ⊢ stackAt s0.sp spqrSendStack ∗ A.pool lim (M.stepEvents evs st) sf ∗ Frame)) := by
  have hsp_align : (s.sp &&& 15#64 == 0#64) = true := by
    rw [hsp]; exact spAligned_sub s0.sp 0x1f80#64 hsp0_align (by decide)
  have hstep1 := step_epilogue_31a3c_placed hdealloc s st vn x23
    (memRegion s.sp 0x30 ∗ chainOrigSlotAt s.sp x23 ∗ memRegion (s.sp + 0xb0#64) (0x1f20 - 0xb0) ∗
      spqrSendSavedRegs s.sp s0 ∗ Frame) hpc hrun hx23 hsp_align
  refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) (SepWP.seq hstep1 ?_)
  intro s1 P1 hpc1 _ ⟨evs, hevs, _, hrun1, htr1, hsp1, hx23_1, hvregs1, hP1⟩
  have hjoin : memRegion (s.sp + 0x30#64) 48 ∗ A.pool lim (M.stepEvents evs st) s1 ∗
      stackAt s.sp spqrSendCalleeStack ∗
      (memRegion s.sp 0x30 ∗ chainOrigSlotAt s.sp x23 ∗ memRegion (s.sp + 0xb0#64) (0x1f20 - 0xb0) ∗
        spqrSendSavedRegs s.sp s0 ∗ Frame) ⊢
      memRegion s1.sp 0x60 ∗ chainOrigSlotAt s1.sp x23 ∗ memRegion (s1.sp + 0xb0#64) (0x1f20 - 0xb0) ∗
        stackAt s1.sp spqrSendCalleeStack ∗ spqrSendSavedRegs s1.sp s0 ∗
        (A.pool lim (M.stepEvents evs st) s1 ∗ Frame) := by
    rw [hsp1, ProofLib.memRegion_split' (b := s.sp) (n := 0x30) (k := 48) (b' := s.sp + 0x30#64) rfl rfl (by decide)]
    exact Entails.of_eq (by sep_ac_rfl)
  refine SepWP.weaken_pre (Entails.trans hP1 hjoin)
    (SepWP.mono (step_epilogue_from_31a54_placed s0 s1 x23 (A.pool lim (M.stepEvents evs st) s1 ∗ Frame)
      hpc1 hrun1 (hsp1.trans hsp) hx23_1 hsp0_align (hvregs1.trans hvregs)) ?_)
  intro sf Q _ _ ⟨hvmf, hrunf, htrf, hspf, hcsf, hQ⟩
  refine ⟨evs, hevs, hrunf, htrf.trans htr1, hspf, hcsf, ?_⟩
  rw [A.pool_of_vmPreserved hvmf]; exact Entails.trans hQ (Entails.of_eq (by sep_ac_rfl))

/-! ## 2. Chain Resolution Composition (`+3196 -> +4000 / +4576 / panic`) -/

private theorem optEpochSecretRegSlotAt_some_ne (A : RustAlloc) (sp x21 x27 : BitVec 64) (es : EpochSecret) :
    optEpochSecretRegSlotAt A sp x21 x27 (some es) ⊢
      ⌜x21 ≠ noneCap⌝ ∗ optEpochSecretRegSlotAt A sp x21 x27 (some es) := by
  dsimp only [optEpochSecretRegSlotAt]; apply Entails.pure_left; intro hne
  exact Entails.pure_right hne (Entails.pure_right hne (Entails.refl _))

private theorem sendChainPostPlaced_congr_frame {M : AllocCostModel} {F : ShaCompress}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (Env : List AllocEvent → Prop)
    (s0 : State) (sp ret x23 : BitVec 64) (st1 : States spqrPolyApi (spqrAuthApi F))
    {Fr1 Fr2 : SepProp} (hFr : Fr1 = Fr2) (res : SpqrApiResult (BitVec 32 × Bytes × Option ChainPB)) :
    sendChainPostPlaced A lim st Env s0 sp ret x23 st1 Fr1 res =
      sendChainPostPlaced A lim st Env s0 sp ret x23 st1 Fr2 res := by subst hFr; rfl

theorem step_chain_resolve_314d8_to_7fc_placed {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {F : ShaCompress} (hkdf : HkdfFn) {ext : String → Option (State → State)}
    (hpanic : ext "_RNvNtCskxtBwYRO61I_4core9panicking5panic" = some Rust.panicked)
    (hpanic_sub : ext "_RNvNtNtCskxtBwYRO61I_4core9panicking11panic_const24panic_const_sub_overflow" = some Rust.panicked)
    (hdealloc : DeallocOkPlaced M A lim ext)
    (hdrop_slice : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 446) (withLsCodeLoaded lsmpl (dropChainEpochSliceSpec M A lim)))
    (hdrop_states : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 443) (withLsCodeLoaded lsmpl (dropChunkedStatesLocal1PlacedSpec M A lim F)))
    (hfrom_pb : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 364) (withLsCodeRoLoaded lsmpl (chainFromPbSpecX M A lim)))
    (hfrom_vn : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 328) (withLsCodeRoLoaded lsmpl (chainFromVersionNegotiationSpecX hkdf M A lim)))
    (hadd_epoch : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 368) (withLsCodeRoLoaded lsmpl (chainAddEpochSpecX hkdf M A lim)))
    (hsend_key : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 367) (withLsCodeRoLoaded lsmpl (chainSendKeySpecX hkdf M A lim)))
    (hinto_pb : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 365) (withLsCodeRoLoaded lsmpl (chainIntoPbSpecX M A lim)))
    (s0 s : State) (st : M.σ) (ret x21 x27 x23 : BitVec 64)
    (chain : Option ChainPB) (hchain_raw : optRaw rawChain chain + 296 ≤ 2 ^ 54)
    (vn : Option VersionNegotiationPB) (key : Option EpochSecret) (msgEpoch : Epoch)
    (st1 : States spqrPolyApi (spqrAuthApi F)) (Frame Fr : SepProp) (φ_out : State → Prop)
    (hFit : FitsEnv M lim st (SendChainPhaseEnv hkdf chain vn key msgEpoch))
    (hinv : LibsignalCodeRoLoaded lsmpl s.mem) (hpc : s.pc = spqrSendPlacedEntry + 3196#64)
    (hrun : s.status = .Running) (htr : s.trace = s0.trace)
    (hx23_none : x23 = noneCap ↔ chain = none) (hpstate : s.pstate = addsPState64 x23 1#64)
    (hx19 : s.readReg64 .x19 = ret) (hx21 : s.readReg64 .x21 = x21)
    (hx22 : s.readReg64 .x22 = msgEpoch) (hx23 : s.readReg64 .x23 = x23)
    (hx25 : s.readReg64 .x25 = s.sp + 0x550#64) (hx26 : s.readReg64 .x26 = s.sp + 0x1260#64)
    (hx27 : s.readReg64 .x27 = x27) (hx28 : s.readReg64 .x28 = s.sp + 0x1060#64)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hφ : ∀ sf : State, (sendChainPhase hkdf chain vn key msgEpoch).isPanic = true ∧ sf.trace = s0.trace → φ_out sf)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0 := by simp only [wp_norm, arm64_norm, *]) :
    SepWPp (spqrSendPlacedProg ext) (sendChainTargetPCPlaced (sendChainPhase hkdf chain vn key msgEpoch)) s
      (optChainPBAt A.repAlloc (s.sp + 0x60#64) chain ∗
        optVersionNegotiationPBAt A.repAlloc (s.sp + 0x30#64) vn ∗
        optEpochSecretRegSlotAt A.repAlloc s.sp x21 x27 key ∗
        memRegion (s.sp + 0x590#64) 88 ∗ memRegion (s.sp + 0x1260#64) 88 ∗
        memRegion (s.sp + 0x1060#64) 80 ∗ memRegion (s.sp + 0xcf0#64) 80 ∗ memRegion (s.sp + 0xd40#64) 80 ∗
        memRegion (s.sp + 0xde0#64) 80 ∗ memRegion (s.sp + 0xd90#64) 72 ∗ memRegion (s.sp + 0x28#64) 8 ∗
        memRegion (s.sp + 0x8#64) 8 ∗ memRegion ret 72 ∗ chunkedStatesAt A.repAlloc (s.sp + 0x190#64) st1 ∗
        chunkedStatesLocal1JumpTablePlacedAt ∗ A.pool lim st s ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
      (sendChainPostPlaced A lim st (SendChainPhaseEnv hkdf chain vn key msgEpoch) s0 s.sp ret x23 st1
        (chainOrigSlotAt s.sp x23 ∗ optVersionNegotiationPBAt A.repAlloc (s.sp + 0x30#64) vn ∗
          memRegion (s.sp + 0xcf0#64) 80 ∗ memRegion (s.sp + 0xd40#64) 80 ∗
          memRegion (s.sp + 0xde0#64) 80 ∗ memRegion (s.sp + 0x1bc0#64) 16 ∗ Frame)
        (sendChainPhase hkdf chain vn key msgEpoch))
      (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ (⌜φ_out sf⌝ ∗ anyHeap) ∗ Fr)) := by
  cases chain with
  | none =>
    have hx23_eq : x23 = noneCap := hx23_none.mpr rfl
    have hz : s.pstate.z = true := by rw [hpstate, hx23_eq]; exact addsPState64_noneCap_z
    have horig_eq : optChainPBAt A.repAlloc (s.sp + 0x60#64) none = chainOrigSlotAt s.sp x23 := by
      have hx23_eq' : x23 = CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation.noneCap := hx23_eq
      rw [hx23_eq', chainOrigSlotAt_none]
      dsimp only [optChainPBAt, CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation.noneCap, noneCap]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
    rw [horig_eq]; apply of_sepWP_lscro_b1 (mid := spqrSendPlacedEntry + 3568#64) hinv
    refine SepWP.mono (step_branch_chain_none_314d8_placed s _ hpc hrun hz) ?_
    rintro s1 P1 hpc1 hrun1 ⟨hvm1, hs1, rfl⟩ hinv1
    rcases setPC_preserves hs1 with ⟨hsp1, htr1, hvregs1, hreg1⟩; rw [← A.pool_of_vmPreserved hvm1]
    have hx19_1 : s1.readReg64 .x19 = ret := (hreg1 .x19).trans hx19
    have hx21_1 : s1.readReg64 .x21 = x21 := (hreg1 .x21).trans hx21
    have hx22_1 : s1.readReg64 .x22 = msgEpoch := (hreg1 .x22).trans hx22
    have hx23_1 : s1.readReg64 .x23 = x23 := (hreg1 .x23).trans hx23
    have hx25_1 : s1.readReg64 .x25 = s.sp + 0x550#64 := (hreg1 .x25).trans hx25
    have hx26_1 : s1.readReg64 .x26 = s.sp + 0x1260#64 := (hreg1 .x26).trans hx26
    have hx27_1 : s1.readReg64 .x27 = x27 := (hreg1 .x27).trans hx27
    have hx28_1 : s1.readReg64 .x28 = s.sp + 0x1060#64 := (hreg1 .x28).trans hx28
    have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by rw [hsp1]; exact hsp_align
    cases vn with
    | none =>
      have heq_ph : sendChainPhase hkdf none none key msgEpoch = .error (.err .chainNotAvailable) := rfl
      rw [heq_ph]
      have hstep := step_vn_none_3164c_to_31a3c_placed hdealloc hdrop_states s1 st ret x21 x27 x23 st1 key
        (chainOrigSlotAt s.sp x23 ∗ memRegion (s.sp + 0x590#64) 88 ∗ memRegion (s.sp + 0x1260#64) 88 ∗
          memRegion (s.sp + 0x1060#64) 80 ∗ memRegion (s.sp + 0xcf0#64) 80 ∗ memRegion (s.sp + 0xd40#64) 80 ∗
          memRegion (s.sp + 0xde0#64) 80 ∗ memRegion (s.sp + 0xd90#64) 72 ∗ memRegion (s.sp + 0x28#64) 8 ∗
          memRegion (s.sp + 0x8#64) 8 ∗ Frame)
        hinv1.1 hpc1 hrun1 hx19_1 hx21_1 hx23_1 hx27_1 hsp1_align
      rw [hsp1] at hstep; apply of_sepWP_lscro_b1 (mid := spqrSendPlacedEntry + 4576#64) hinv1
      refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) (SepWP.mono hstep ?_)
      rintro sf Qf hpcf _ ⟨evs, hevs, hrunf, htrf, hspf, hx23f, hvregsf, hQf⟩ hinvf
      exact SepWPp.done hpcf hrunf
        ⟨evs, hevs, hrunf, htrf.trans (htr1.trans htr), hspf, hinvf, hx23f,
         hvregsf.trans (hvregs1.trans hvregs), Entails.trans hQf (Entails.of_eq (by sep_ac_rfl))⟩
    | some v =>
      by_cases hgt : BitVec.slt 0#32 v.minVersion = true
      · have hFit_vn : FitsEnv M lim st (ChainFromVersionNegotiationEnv v) := by
          cases hfvn_fit : chainFromVersionNegotiation hkdf v with
          | error _ =>
            exact (FitsEnv.mono (E₁ := SeqEnv (ChainFromVersionNegotiationEnv v) FreeOnlyEvs)
              (fun evs he => by unfold SendChainPhaseEnv; simp only [hgt, ↓reduceIte, hfvn_fit]; exact he) hFit).seq_left
          | ok c0 =>
            exact (FitsEnv.mono (E₁ := SeqEnv (ChainFromVersionNegotiationEnv v) (SendStepChainEnv hkdf (some c0) key msgEpoch))
              (fun evs he => by unfold SendChainPhaseEnv; simp only [hgt, ↓reduceIte, hfvn_fit]; exact he) hFit).seq_left
        have hpre_vn := step_pre_from_vn_3164c_placed (M := M) (A := A) (ext := ext) s1 v
          (chainOrigSlotAt s.sp x23 ∗ optEpochSecretRegSlotAt A.repAlloc s.sp x21 x27 key ∗
            memRegion (s.sp + 0x590#64) 88 ∗ memRegion (s.sp + 0x1260#64) 88 ∗
            memRegion (s.sp + 0x1060#64) 80 ∗ memRegion (s.sp + 0xcf0#64) 80 ∗
            memRegion (s.sp + 0xd40#64) 80 ∗ memRegion (s.sp + 0xde0#64) 80 ∗
            memRegion (s.sp + 0xd90#64) 72 ∗ memRegion (s.sp + 0x28#64) 8 ∗ memRegion (s.sp + 0x8#64) 8 ∗
            memRegion ret 72 ∗ chunkedStatesAt A.repAlloc (s.sp + 0x190#64) st1 ∗
            chunkedStatesLocal1JumpTablePlacedAt ∗ A.pool lim st s1 ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
          hpc1 hrun1 hgt hsp1_align
        rw [hsp1] at hpre_vn; apply of_sepWP_lscro_b1 (mid := lsmpl.base 328) hinv1
        refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) (SepWP.mono hpre_vn ?_)
        rintro s2 P2 hpc2 hrun2 ⟨hvm2, _, htr2, hsp2, hx0_2, hx8_2, hx30_2, hx19_2, _, hx21_2, hx22_2, hx23_2, _, hx25_2, hx26_2, hx27_2, hx28_2, hvregs2, hP2⟩ hinv2
        refine SepWPp.weaken_pre hP2 ?_; rw [← A.pool_of_vmPreserved hvm2]
        apply SepWPp.exists_elim; intro pin
        have htr2_0 : s2.trace = s0.trace := htr2.trans (htr1.trans htr)
        let x_vn : ChainFromVersionNegotiationCall := ⟨s.sp + 0x1260#64, s.sp + 0x30#64, pin, v⟩
        refine call_lscro_calleeStack_evs_anyPanic (s.sp) chainFromVersionNegotiationStackX (by decide)
          (x := (x_vn, st))
          (T_pre := memRegion (s.sp + 0x1260#64) 88 ∗ versionNegotiationPBAt A.repAlloc pin (s.sp + 0x30#64) v ∗ A.pool lim st s2)
          (T_post := fun evs₁ sf => chainResultAt A.repAlloc (s.sp + 0x1260#64) (chainFromVersionNegotiation hkdf v) ∗
            versionNegotiationPBAt A.repAlloc pin (s.sp + 0x30#64) v ∗ A.pool lim (M.stepEvents evs₁ st) sf)
          (F := chainOrigSlotAt s.sp x23 ∗ optEpochSecretRegSlotAt A.repAlloc s.sp x21 x27 key ∗
            memRegion (s.sp + 0x590#64) 88 ∗ memRegion (s.sp + 0x1060#64) 80 ∗
            memRegion (s.sp + 0xcf0#64) 80 ∗ memRegion (s.sp + 0xd40#64) 80 ∗
            memRegion (s.sp + 0xde0#64) 80 ∗ memRegion (s.sp + 0xd90#64) 72 ∗
            memRegion (s.sp + 0x28#64) 8 ∗ memRegion (s.sp + 0x8#64) 8 ∗ memRegion ret 72 ∗
            chunkedStatesAt A.repAlloc (s.sp + 0x190#64) st1 ∗ chunkedStatesLocal1JumpTablePlacedAt ∗ Frame)
          (φ_pre := s2.readReg64 .x8 = x_vn.out ∧ s2.readReg64 .x0 = x_vn.vPtr ∧
            FitsEnv M lim st (ChainFromVersionNegotiationEnv x_vn.v))
          (φ_post := fun evs₁ sf => sf.trace = s2.trace ∧ ChainFromVersionNegotiationEnv x_vn.v evs₁)
          (φ_pan := fun _ => False) hfrom_vn hinv2 hpc2 hrun2 hsp2 hsp_align hx30_2
          (by dsimp only [chainFromVersionNegotiationSpecX, x_vn]; sep_ac_rfl)
          ⟨hx8_2, hx0_2, hFit_vn⟩ (by sep_ac_rfl) (fun _ _ => rfl)
          (fun _ => by change ⌜False⌝ = _; symm; exact pure_false_sepConj _) (fun _ h => h.elim)
          (fun sf => by dsimp only [chainFromVersionNegotiationSpecX, x_vn]; exact congrArg sepExists (funext fun _ => by sep_ac_rfl)) ?_
        intro evs₁ s3 hpc3 hrun3 hsp3 ⟨htr3, h_vn1⟩ hinv3 hx19_3 _ hx21_3 hx22_3 hx23_3 _ hx25_3 hx26_3 hx27_3 hx28_3 hvregs3
        have hsp3_align : (s3.sp &&& 15#64 == 0#64) = true := by rw [hsp3]; exact hsp_align
        have htr3_0 : s3.trace = s0.trace := htr3.trans htr2_0
        have hvregs3_0 : calleeSavedVRegs s3 = calleeSavedVRegs s0 := hvregs3.trans (hvregs2.trans (hvregs1.trans hvregs))
        have hx19_30 : s3.readReg64 .x19 = ret := hx19_3.trans (hx19_2.trans hx19_1)
        have hx21_30 : s3.readReg64 .x21 = x21 := hx21_3.trans (hx21_2.trans hx21_1)
        have hx22_30 : s3.readReg64 .x22 = msgEpoch := hx22_3.trans (hx22_2.trans hx22_1)
        have hx23_30 : s3.readReg64 .x23 = x23 := hx23_3.trans (hx23_2.trans hx23_1)
        have hx25_30 : s3.readReg64 .x25 = s3.sp + 0x550#64 := by rw [hsp3]; exact hx25_3.trans (hx25_2.trans hx25_1)
        have hx26_30 : s3.readReg64 .x26 = s3.sp + 0x1260#64 := by rw [hsp3]; exact hx26_3.trans (hx26_2.trans hx26_1)
        have hx27_30 : s3.readReg64 .x27 = x27 := hx27_3.trans (hx27_2.trans hx27_1)
        have hx28_30 : s3.readReg64 .x28 = s3.sp + 0x1060#64 := by rw [hsp3]; exact hx28_3.trans (hx28_2.trans hx28_1)
        refine SepWPp.weaken_pre (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (vn_some_pack A.repAlloc pin (s.sp + 0x30#64) v))))) ?_
        cases hfvn : chainFromVersionNegotiation hkdf v with
        | error err =>
          have heq_ph : sendChainPhase hkdf none (some v) key msgEpoch = .error (.err err) := by
            unfold sendChainPhase sendResolveChain; simp [Version.toI32, hgt, hfvn, SpqrApiResult.ofError]; rfl
          rw [heq_ph]; dsimp only [chainResultAt]; rw [memRegion_590_88_eq_24_64 s.sp]
          have hstep := step_from_vn_err_31674_to_31a3c_placed hdealloc hdrop_states
            s3 (M.stepEvents evs₁ st) ret x21 x27 x23 err st1 key
            (optVersionNegotiationPBAt A.repAlloc (s.sp + 0x30#64) (some v) ∗
              chainOrigSlotAt s.sp x23 ∗ memRegion (s.sp + 0x5a8#64) 64 ∗ memRegion (s.sp + 0x1060#64) 80 ∗
              memRegion (s.sp + 0xcf0#64) 80 ∗ memRegion (s.sp + 0xd40#64) 80 ∗ memRegion (s.sp + 0xde0#64) 80 ∗
              memRegion (s.sp + 0xd90#64) 72 ∗ memRegion (s.sp + 0x28#64) 8 ∗ memRegion (s.sp + 0x8#64) 8 ∗ Frame)
            hinv3.1 hpc3 hrun3 hx19_30 hx21_30 hx23_30 hx26_30 hx27_30 hsp3_align
          rw [hsp3] at hstep; apply of_sepWP_lscro_b1 (mid := spqrSendPlacedEntry + 4576#64) hinv3
          refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) (SepWP.mono hstep ?_)
          rintro sf Qf hpcf _ ⟨evs₂, hevs₂, hrunf, htrf, hspf, hx23f, hvregsf, hQf⟩ hinvf
          have hEnv_err : SendChainPhaseEnv hkdf none (some v) key msgEpoch (evs₁ ++ evs₂) := by
            unfold SendChainPhaseEnv; simp only [hgt, ↓reduceIte, hfvn]; exact SeqEnv.append h_vn1 hevs₂
          refine SepWPp.done hpcf hrunf
            ⟨evs₁ ++ evs₂, hEnv_err, hrunf, htrf.trans htr3_0, hspf, hinvf, hx23f, hvregsf.trans hvregs3_0, ?_⟩
          rw [M.stepEvents_append, memRegion_590_88_eq_24_64 s.sp]
          exact Entails.trans hQf (Entails.of_eq (by sep_ac_rfl))
        | ok c0 =>
          have hres : sendResolveChain hkdf none (some v) = .ok (some c0) := by
            unfold sendResolveChain; simp [Version.toI32, hgt, hfvn, SpqrApiResult.ofError]
          have heq_ph : sendChainPhase hkdf none (some v) key msgEpoch = sendStepChain hkdf (some c0) key msgEpoch := by
            unfold sendChainPhase; rw [hres]; rfl
          have hc0_len : c0.links.length ≤ 2 ^ 54 :=
            Nat.le_trans (chain_links_length_le_rawChain c0) (Nat.le_trans (sendResolveChain_raw_le hkdf none (some v) hres) hchain_raw)
          have hFit_step : FitsEnv M lim (M.stepEvents evs₁ st) (SendStepChainEnv hkdf (some c0) key msgEpoch) :=
            (FitsEnv.mono (E₁ := SeqEnv (ChainFromVersionNegotiationEnv v) (SendStepChainEnv hkdf (some c0) key msgEpoch))
              (fun evs he => by unfold SendChainPhaseEnv; simp only [hgt, ↓reduceIte, hfvn]; exact he) hFit).seq_right h_vn1
          rw [heq_ph, sendChainPostPlaced_congr_frame A lim st (SendChainPhaseEnv hkdf none (some v) key msgEpoch) s0 s.sp ret x23 st1
            (Fr2 := memRegion (s.sp + 0x1bc0#64) 16 ∗ (chainOrigSlotAt s.sp x23 ∗
              optVersionNegotiationPBAt A.repAlloc (s.sp + 0x30#64) (some v) ∗
              memRegion (s.sp + 0xcf0#64) 80 ∗ memRegion (s.sp + 0xd40#64) 80 ∗ memRegion (s.sp + 0xde0#64) 80 ∗ Frame))
            (by sep_ac_rfl)]
          dsimp only [chainResultAt]
          have hstep_ok := step_post_from_vn_ok_31674_placed (M := M) (A := A) (ext := ext) s3 c0
            (optVersionNegotiationPBAt A.repAlloc (s.sp + 0x30#64) (some v) ∗
              chainOrigSlotAt s.sp x23 ∗ optEpochSecretRegSlotAt A.repAlloc s.sp x21 x27 key ∗
              memRegion (s.sp + 0x1060#64) 80 ∗ memRegion (s.sp + 0xd40#64) 80 ∗
              memRegion (s.sp + 0xd90#64) 72 ∗ memRegion (s.sp + 0x28#64) 8 ∗ memRegion (s.sp + 0x8#64) 8 ∗
              memRegion ret 72 ∗ chunkedStatesAt A.repAlloc (s.sp + 0x190#64) st1 ∗
              chunkedStatesLocal1JumpTablePlacedAt ∗ A.pool lim (M.stepEvents evs₁ st) s3 ∗
              stackAt s.sp spqrSendCalleeStack ∗ Frame)
            hpc3 hrun3 hx25_30 hx26_30 hsp3_align
          rw [hsp3] at hstep_ok; apply of_sepWP_lscro_b1 (mid := spqrSendPlacedEntry + 3420#64) hinv3
          refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) (SepWP.mono hstep_ok ?_)
          rintro s4 P4 hpc4 hrun4 ⟨hvm4, _, htr4, hsp4, hpst4, hx20_4, hx19_4, hx21_4, hx22_4, hx23_4, _, _, hx26_4, hx27_4, hx28_4, hvregs4, hP4⟩ hinv4
          have hstep_5b8 := step_chain_5b8_to_7fc_placed hkdf hpanic_sub hdealloc hdrop_slice hdrop_states
            hadd_epoch hsend_key hinto_pb s0 s4 (M.stepEvents evs₁ st) ret x21 x27 x23 c0 hc0_len key msgEpoch st1
            (chainOrigSlotAt s.sp x23 ∗ optVersionNegotiationPBAt A.repAlloc (s.sp + 0x30#64) (some v) ∗
              memRegion (s.sp + 0xcf0#64) 80 ∗ memRegion (s.sp + 0xd40#64) 80 ∗ memRegion (s.sp + 0xde0#64) 80 ∗ Frame)
            Fr φ_out hFit_step hinv4 hpc4 hrun4 (htr4.trans htr3_0)
            (by rw [hx21_30] at hpst4; exact hpst4)
            (hx19_4.trans hx19_30) (hx21_4.trans hx21_30) (hx22_4.trans hx22_30) (hx23_4.trans hx23_30)
            (by rw [hsp4, ← hsp3]; exact hx26_4.trans hx26_30) (hx27_4.trans hx27_30)
            (by rw [hsp4, ← hsp3]; exact hx28_4.trans hx28_30)
            (flag_of_csinc_315b8 (hx21_4.trans hx21_30) (by rw [hx21_30] at hx20_4; exact hx20_4))
            (by rw [hsp4]; exact hsp_align) (by rwa [heq_ph] at hφ) (hvregs4.trans hvregs3_0)
          rw [hsp4, A.pool_of_vmPreserved hvm4] at hstep_5b8
          refine sepWPp_mono_post (fun sf Pf hQ => ?_)
            (SepWPp.weaken_pre (Entails.trans hP4 (Entails.of_eq (by sep_ac_rfl))) hstep_5b8)
          refine sendChainPostPlaced_mono (fun evs he => ?_) (sendChainPostPlaced_step h_vn1 hQ)
          unfold SendChainPhaseEnv; simp only [hgt, ↓reduceIte, hfvn]; exact he
      · have hle : BitVec.slt 0#32 v.minVersion = false := Bool.eq_false_iff.mpr hgt
        have hres : sendResolveChain hkdf none (some v) = .ok none := by
          unfold sendResolveChain; simp [Version.toI32, hle]; rfl
        have heq_ph : sendChainPhase hkdf none (some v) key msgEpoch = sendStepChain hkdf none key msgEpoch := by
          unfold sendChainPhase; rw [hres]; rfl
        rw [heq_ph]
        let Mid := memRegion (s.sp + 0x590#64) 88 ∗ memRegion (s.sp + 0x1260#64) 88 ∗
          memRegion (s.sp + 0x1060#64) 80 ∗ memRegion (s.sp + 0xcf0#64) 80 ∗
          memRegion (s.sp + 0xd40#64) 80 ∗ memRegion (s.sp + 0xde0#64) 80
        let Slots := memRegion (s.sp + 0xd90#64) 72 ∗ memRegion (s.sp + 0x28#64) 8 ∗ memRegion (s.sp + 0x8#64) 8
        have hstep_le := step_from_vn_le_zero_3164c_placed (M := M) (A := A) (ext := ext) s1 v
          (chainOrigSlotAt s.sp x23 ∗ optEpochSecretRegSlotAt A.repAlloc s.sp x21 x27 key ∗ Mid ∗ Slots ∗
            memRegion ret 72 ∗ chunkedStatesAt A.repAlloc (s.sp + 0x190#64) st1 ∗
            chunkedStatesLocal1JumpTablePlacedAt ∗ A.pool lim st s1 ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
          hpc1 hrun1 hle hsp1_align
        rw [hsp1] at hstep_le; apply of_sepWP_lscro_b1 (mid := spqrSendPlacedEntry + 3964#64) hinv1
        refine SepWP.weaken_pre (Entails.of_eq (by dsimp only [Mid, Slots]; sep_ac_rfl)) (SepWP.mono hstep_le ?_)
        rintro s2 P2 hpc2 hrun2 ⟨hvm2, _, htr2, hsp2, hx19_2, _, hx21_2, _, hx23_2, _, _, hx26_2, _, hx28_2, hvregs2, hP2⟩ hinv2
        have htr2_0 : s2.trace = s0.trace := htr2.trans (htr1.trans htr)
        have hvregs2_0 : calleeSavedVRegs s2 = calleeSavedVRegs s0 := hvregs2.trans (hvregs1.trans hvregs)
        have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2]; exact hsp_align
        refine SepWPp.weaken_pre hP2 ?_; rw [← A.pool_of_vmPreserved hvm2]
        let Tail2 := memRegion ret 72 ∗ chunkedStatesAt A.repAlloc (s.sp + 0x190#64) st1 ∗
          chunkedStatesLocal1JumpTablePlacedAt ∗ A.pool lim st s2 ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame
        cases key with
        | none =>
          have heq_st : sendStepChain hkdf none none msgEpoch = .ok (0#32, [], none) := rfl
          rw [heq_st]; dsimp only [optEpochSecretRegSlotAt]
          have hpull : optVersionNegotiationPBAt A.repAlloc (s.sp + 0x30#64) (some v) ∗
              (chainOrigSlotAt s.sp x23 ∗ (⌜x21 = noneCap⌝ ∗ memRegion (s.sp + 0x1bc0#64) 16) ∗
                Mid ∗ Slots ∗ memRegion ret 72 ∗ chunkedStatesAt A.repAlloc (s.sp + 0x190#64) st1 ∗
                chunkedStatesLocal1JumpTablePlacedAt ∗ A.pool lim st s2 ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame) ⊢
              ⌜x21 = noneCap⌝ ∗ (Slots ∗ (optVersionNegotiationPBAt A.repAlloc (s.sp + 0x30#64) (some v) ∗
                chainOrigSlotAt s.sp x23 ∗ memRegion (s.sp + 0x1bc0#64) 16 ∗ Mid ∗ Tail2)) :=
            Entails.of_eq (by dsimp only [Mid, Slots, Tail2]; sep_ac_rfl)
          refine SepWPp.weaken_pre hpull ?_
          apply pure_elim_focus_b1 (x21 = noneCap); intro hx21_none
          have hstep_ok := step_min_version_zero_ok_317d8_placed (M := M) (A := A) (ext := ext) s2
            (optVersionNegotiationPBAt A.repAlloc (s.sp + 0x30#64) (some v) ∗
              chainOrigSlotAt s.sp x23 ∗ memRegion (s.sp + 0x1bc0#64) 16 ∗ Mid ∗ Tail2)
            hpc2 hrun2 (hx21_2.trans (hx21_1.trans hx21_none)) hsp2_align
          rw [hsp2] at hstep_ok; dsimp only [Slots]
          apply of_sepWP_lscro_b1 (mid := spqrSendPlacedEntry + 4000#64) hinv2
          refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) (SepWP.mono hstep_ok ?_)
          rintro sf Qf hpcf _ ⟨hvmf, hrunf, htrf, hspf, hx24f, hx22f, _, _, hx19f, hx21f, hx23f, hx26f, _, hx28f, hvregsf, hQf⟩ hinvf
          have hEnv_nil : SendChainPhaseEnv hkdf none (some v) none msgEpoch [] := by
            unfold SendChainPhaseEnv SendStepChainEnv; simp [hgt]
          refine SepWPp.done hpcf hrunf
            ⟨[], hEnv_nil, hrunf, htrf.trans htr2_0, hspf, hinvf,
             hx19f.trans (hx19_2.trans hx19_1), hx22f, hx23f.trans (hx23_2.trans hx23_1),
             hx24f, hx26f.trans (hx26_2.trans hx26_1), hx28f.trans (hx28_2.trans hx28_1),
             Or.inl (hx21f.trans (hx21_2.trans (hx21_1.trans hx21_none))), hvregsf.trans hvregs2_0, ?_⟩
          dsimp only [Mid, Tail2] at hQf; simp only [M.stepEvents_nil]
          rw [A.pool_of_vmPreserved hvmf]; exact Entails.trans hQf (Entails.of_eq (by sep_ac_rfl))
        | some es =>
          have hpull : optVersionNegotiationPBAt A.repAlloc (s.sp + 0x30#64) (some v) ∗
              (chainOrigSlotAt s.sp x23 ∗ optEpochSecretRegSlotAt A.repAlloc s.sp x21 x27 (some es) ∗
                Mid ∗ Slots ∗ memRegion ret 72 ∗ chunkedStatesAt A.repAlloc (s.sp + 0x190#64) st1 ∗
                chunkedStatesLocal1JumpTablePlacedAt ∗ A.pool lim st s2 ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame) ⊢
              ⌜x21 ≠ noneCap⌝ ∗ (optVersionNegotiationPBAt A.repAlloc (s.sp + 0x30#64) (some v) ∗
                chainOrigSlotAt s.sp x23 ∗ optEpochSecretRegSlotAt A.repAlloc s.sp x21 x27 (some es) ∗
                Mid ∗ Slots ∗ Tail2) :=
            Entails.trans
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (optEpochSecretRegSlotAt_some_ne A.repAlloc s.sp x21 x27 es))))
              (Entails.of_eq (by dsimp only [Tail2]; sep_ac_rfl))
          refine SepWPp.weaken_pre hpull ?_
          apply pure_elim_focus_b1 (x21 ≠ noneCap); intro hx21_ne
          refine step_panic_key_without_chain_317d8_placed ext hpanic hinv2 hpc2 hrun2
            (by rw [hx21_2, hx21_1]; exact hx21_ne) fun sf htr_f => ?_
          exact hφ sf ⟨by rw [heq_ph]; rfl, htr_f.trans htr2_0⟩
  | some pb =>
    have hx23_ne : x23 ≠ noneCap := fun h => by have := hx23_none.mp h; contradiction
    have hz : s.pstate.z = false := by rw [hpstate]; exact addsPState64_z_false_of_ne_noneCap hx23_ne
    dsimp only [optChainPBAt]; rw [memRegion_590_88_eq_80_8 s.sp]
    have hpre_pb := step_pre_from_pb_314d8_placed (M := M) (A := A) (ext := ext) s pb
      (optVersionNegotiationPBAt A.repAlloc (s.sp + 0x30#64) vn ∗
        optEpochSecretRegSlotAt A.repAlloc s.sp x21 x27 key ∗
        memRegion (s.sp + 0x5e0#64) 8 ∗ memRegion (s.sp + 0x1260#64) 88 ∗ memRegion (s.sp + 0x1060#64) 80 ∗
        memRegion (s.sp + 0xcf0#64) 80 ∗ memRegion (s.sp + 0xd40#64) 80 ∗ memRegion (s.sp + 0xde0#64) 80 ∗
        memRegion (s.sp + 0xd90#64) 72 ∗ memRegion (s.sp + 0x28#64) 8 ∗ memRegion (s.sp + 0x8#64) 8 ∗ memRegion ret 72 ∗
        chunkedStatesAt A.repAlloc (s.sp + 0x190#64) st1 ∗ chunkedStatesLocal1JumpTablePlacedAt ∗
        A.pool lim st s ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
      hpc hrun hz (by rw [hx23]; exact hx23_ne) hsp_align
    apply of_sepWP_lscro_b1 (mid := lsmpl.base 364) hinv
    refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) (SepWP.mono hpre_pb ?_)
    rintro s1 P1 hpc1 hrun1 ⟨hvm1, _, htr1, hsp1, hx0_1, hx8_1, hx30_1, hx19_1, _, hx21_1, hx22_1, hx23_1, _, hx25_1, hx26_1, hx27_1, hx28_1, hvregs1, hP1⟩ hinv1
    rw [hx23] at hP1; refine SepWPp.weaken_pre hP1 ?_; rw [← A.pool_of_vmPreserved hvm1]
    apply SepWPp.exists_elim; intro gPb
    have htr1_0 : s1.trace = s0.trace := htr1.trans htr
    have hlr_pb : LsRetAddr624 (s1.readReg64 .lr) :=
      hx30_1.symm ▸ lsRetAddr624_base_add 427 3252#64 (by decide) (by decide)
    let x_pb : ChainFromPbCall := ⟨s.sp + 0x1260#64, s.sp + 0x590#64, gPb, pb⟩
    refine call_lscro_calleeStack_evs_anyPanic (s.sp) chainFromPbStackX (by decide) (x := (x_pb, st))
      (T_pre := memRegion (s.sp + 0x1260#64) 88 ∗ chainPBAt A.repAlloc gPb (s.sp + 0x590#64) pb ∗ A.pool lim st s1)
      (T_post := fun evs₁ sf => chainResultAt A.repAlloc (s.sp + 0x1260#64) (Chain.fromPb pb) ∗
        memRegion (s.sp + 0x590#64) 80 ∗ A.pool lim (M.stepEvents evs₁ st) sf)
      (F := chainOrigSlotAt s.sp x23 ∗ optVersionNegotiationPBAt A.repAlloc (s.sp + 0x30#64) vn ∗
        optEpochSecretRegSlotAt A.repAlloc s.sp x21 x27 key ∗ memRegion (s.sp + 0x5e0#64) 8 ∗
        memRegion (s.sp + 0x1060#64) 80 ∗ memRegion (s.sp + 0xcf0#64) 80 ∗ memRegion (s.sp + 0xd40#64) 80 ∗
        memRegion (s.sp + 0xde0#64) 80 ∗ memRegion (s.sp + 0xd90#64) 72 ∗ memRegion (s.sp + 0x28#64) 8 ∗
        memRegion (s.sp + 0x8#64) 8 ∗ memRegion ret 72 ∗
        chunkedStatesAt A.repAlloc (s.sp + 0x190#64) st1 ∗ chunkedStatesLocal1JumpTablePlacedAt ∗ Frame)
      (φ_pre := s1.readReg64 .x8 = x_pb.out ∧ s1.readReg64 .x0 = x_pb.pbPtr ∧ LsRetAddr624 (s1.readReg64 .lr))
      (φ_post := fun evs₁ sf => sf.trace = s1.trace ∧ FreeOnlyEvs evs₁)
      (φ_pan := fun _ => False) hfrom_pb hinv1 hpc1 hrun1 hsp1 hsp_align hx30_1
      (by dsimp only [chainFromPbSpecX, x_pb]; sep_ac_rfl) ⟨hx8_1, hx0_1, hlr_pb⟩ (by sep_ac_rfl) (fun _ _ => rfl)
      (fun _ => by change ⌜False⌝ = _; symm; exact pure_false_sepConj _) (fun _ h => h.elim)
      (fun sf => by dsimp only [chainFromPbSpecX, x_pb]; exact congrArg sepExists (funext fun _ => by sep_ac_rfl)) ?_
    intro evs₁ s2 hpc2 hrun2 hsp2 ⟨htr2, h_pb1⟩ hinv2 hx19_2 _ hx21_2 hx22_2 hx23_2 _ hx25_2 hx26_2 hx27_2 hx28_2 hvregs2
    have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2]; exact hsp_align
    have htr2_0 : s2.trace = s0.trace := htr2.trans htr1_0
    have hvregs2_0 : calleeSavedVRegs s2 = calleeSavedVRegs s0 := hvregs2.trans (hvregs1.trans hvregs)
    have hx19_20 : s2.readReg64 .x19 = ret := hx19_2.trans (hx19_1.trans hx19)
    have hx21_20 : s2.readReg64 .x21 = x21 := hx21_2.trans (hx21_1.trans hx21)
    have hx22_20 : s2.readReg64 .x22 = msgEpoch := hx22_2.trans (hx22_1.trans hx22)
    have hx23_20 : s2.readReg64 .x23 = x23 := hx23_2.trans (hx23_1.trans hx23)
    have hx25_20 : s2.readReg64 .x25 = s2.sp + 0x550#64 := by rw [hsp2]; exact hx25_2.trans (hx25_1.trans hx25)
    have hx26_20 : s2.readReg64 .x26 = s2.sp + 0x1260#64 := by rw [hsp2]; exact hx26_2.trans (hx26_1.trans hx26)
    have hx27_20 : s2.readReg64 .x27 = x27 := hx27_2.trans (hx27_1.trans hx27)
    have hx28_20 : s2.readReg64 .x28 = s2.sp + 0x1060#64 := by rw [hsp2]; exact hx28_2.trans (hx28_1.trans hx28)
    cases hfpb : Chain.fromPb pb with
    | error err =>
      have heq_ph : sendChainPhase hkdf (some pb) vn key msgEpoch = .error (.err err) := by
        unfold sendChainPhase sendResolveChain; simp [hfpb, SpqrApiResult.ofError]; rfl
      rw [heq_ph]; dsimp only [chainResultAt]; rw [memRegion_1060_80_eq_24_56 s.sp]
      have hstep := step_from_pb_err_31510_to_31a3c_placed hdealloc hdrop_states
        s2 (M.stepEvents evs₁ st) ret x21 x27 x23 err st1 key
        (memRegion (s.sp + 0x590#64) 80 ∗ memRegion (s.sp + 0x5e0#64) 8 ∗ chainOrigSlotAt s.sp x23 ∗
          optVersionNegotiationPBAt A.repAlloc (s.sp + 0x30#64) vn ∗
          memRegion (s.sp + 0x1078#64) 56 ∗ memRegion (s.sp + 0xcf0#64) 80 ∗
          memRegion (s.sp + 0xd40#64) 80 ∗ memRegion (s.sp + 0xde0#64) 80 ∗
          memRegion (s.sp + 0xd90#64) 72 ∗ memRegion (s.sp + 0x28#64) 8 ∗ memRegion (s.sp + 0x8#64) 8 ∗ Frame)
        hinv2.1 hpc2 hrun2 hx19_20 hx21_20 hx23_20 hx26_20 hx27_20 hsp2_align
      rw [hsp2] at hstep; apply of_sepWP_lscro_b1 (mid := spqrSendPlacedEntry + 4576#64) hinv2
      refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) (SepWP.mono hstep ?_)
      rintro sf Qf hpcf _ ⟨evs₂, hevs₂, hrunf, htrf, hspf, hx23f, hvregsf, hQf⟩ hinvf
      have hEnv_err : SendChainPhaseEnv hkdf (some pb) vn key msgEpoch (evs₁ ++ evs₂) := by
        unfold SendChainPhaseEnv; simp only [hfpb]; exact FreeOnlyEvs.append h_pb1 hevs₂
      refine SepWPp.done hpcf hrunf
        ⟨evs₁ ++ evs₂, hEnv_err, hrunf, htrf.trans htr2_0, hspf, hinvf, hx23f, hvregsf.trans hvregs2_0, ?_⟩
      rw [M.stepEvents_append, memRegion_590_88_eq_80_8 s.sp, memRegion_1060_80_eq_24_56 s.sp]
      exact Entails.trans hQf (Entails.of_eq (by sep_ac_rfl))
    | ok c0 =>
      have hres : sendResolveChain hkdf (some pb) vn = .ok (some c0) := by
        unfold sendResolveChain; simp [hfpb, SpqrApiResult.ofError]
      have heq_ph : sendChainPhase hkdf (some pb) vn key msgEpoch = sendStepChain hkdf (some c0) key msgEpoch := by
        unfold sendChainPhase; rw [hres]; rfl
      have hc0_len : c0.links.length ≤ 2 ^ 54 :=
        Nat.le_trans (chain_links_length_le_rawChain c0) (Nat.le_trans (sendResolveChain_raw_le hkdf (some pb) vn hres) hchain_raw)
      have hFit_step : FitsEnv M lim (M.stepEvents evs₁ st) (SendStepChainEnv hkdf (some c0) key msgEpoch) :=
        (FitsEnv.mono (E₁ := SeqEnv FreeOnlyEvs (SendStepChainEnv hkdf (some c0) key msgEpoch))
          (fun evs he => by unfold SendChainPhaseEnv; simp only [hfpb]; exact he) hFit).seq_right h_pb1
      rw [heq_ph, sendChainPostPlaced_congr_frame A lim st (SendChainPhaseEnv hkdf (some pb) vn key msgEpoch) s0 s.sp ret x23 st1
        (Fr2 := memRegion (s.sp + 0x1bc0#64) 16 ∗ (chainOrigSlotAt s.sp x23 ∗
          optVersionNegotiationPBAt A.repAlloc (s.sp + 0x30#64) vn ∗
          memRegion (s.sp + 0xcf0#64) 80 ∗ memRegion (s.sp + 0xd40#64) 80 ∗ memRegion (s.sp + 0xde0#64) 80 ∗ Frame))
        (by sep_ac_rfl)]
      dsimp only [chainResultAt]; rw [memRegion_1060_80_eq_24_56 s.sp]
      have hstep_ok := step_post_from_pb_ok_31510_placed (M := M) (A := A) (ext := ext) s2 c0
        (chainOrigSlotAt s.sp x23 ∗ optVersionNegotiationPBAt A.repAlloc (s.sp + 0x30#64) vn ∗
          optEpochSecretRegSlotAt A.repAlloc s.sp x21 x27 key ∗ memRegion (s.sp + 0x1078#64) 56 ∗
          memRegion (s.sp + 0xcf0#64) 80 ∗ memRegion (s.sp + 0xd90#64) 72 ∗ memRegion (s.sp + 0x28#64) 8 ∗
          memRegion (s.sp + 0x8#64) 8 ∗ memRegion ret 72 ∗ chunkedStatesAt A.repAlloc (s.sp + 0x190#64) st1 ∗
          chunkedStatesLocal1JumpTablePlacedAt ∗ A.pool lim (M.stepEvents evs₁ st) s2 ∗
          stackAt s.sp spqrSendCalleeStack ∗ Frame)
        hpc2 hrun2 hx25_20 hx26_20 hsp2_align
      rw [hsp2] at hstep_ok; apply of_sepWP_lscro_b1 (mid := spqrSendPlacedEntry + 3420#64) hinv2
      refine SepWP.weaken_pre (Entails.of_eq (by rw [memRegion_590_88_eq_80_8 s.sp]; sep_ac_rfl)) (SepWP.mono hstep_ok ?_)
      rintro s3 P3 hpc3 hrun3 ⟨hvm3, _, htr3, hsp3, hpst3, hx20_3, hx19_3, hx21_3, hx22_3, hx23_3, _, _, hx26_3, hx27_3, hx28_3, hvregs3, hP3⟩ hinv3
      have hstep_5b8 := step_chain_5b8_to_7fc_placed hkdf hpanic_sub hdealloc hdrop_slice hdrop_states
        hadd_epoch hsend_key hinto_pb s0 s3 (M.stepEvents evs₁ st) ret x21 x27 x23 c0 hc0_len key msgEpoch st1
        (chainOrigSlotAt s.sp x23 ∗ optVersionNegotiationPBAt A.repAlloc (s.sp + 0x30#64) vn ∗
          memRegion (s.sp + 0xcf0#64) 80 ∗ memRegion (s.sp + 0xd40#64) 80 ∗ memRegion (s.sp + 0xde0#64) 80 ∗ Frame)
        Fr φ_out hFit_step hinv3 hpc3 hrun3 (htr3.trans htr2_0)
        (by rw [hx21_20] at hpst3; exact hpst3)
        (hx19_3.trans hx19_20) (hx21_3.trans hx21_20) (hx22_3.trans hx22_20) (hx23_3.trans hx23_20)
        (by rw [hsp3, ← hsp2]; exact hx26_3.trans hx26_20) (hx27_3.trans hx27_20)
        (by rw [hsp3, ← hsp2]; exact hx28_3.trans hx28_20)
        (flag_of_csinc_315b8 (hx21_3.trans hx21_20) (by rw [hx21_20] at hx20_3; exact hx20_3))
        (by rw [hsp3]; exact hsp_align) (by rwa [heq_ph] at hφ) (hvregs3.trans hvregs2_0)
      rw [hsp3, memRegion_1060_80_eq_24_56 s.sp, A.pool_of_vmPreserved hvm3] at hstep_5b8
      refine sepWPp_mono_post (fun sf Pf hQ => ?_)
        (SepWPp.weaken_pre (Entails.trans hP3 (Entails.of_eq (by sep_ac_rfl))) hstep_5b8)
      refine sendChainPostPlaced_mono (fun evs he => ?_) (sendChainPostPlaced_step h_pb1 hQ)
      unfold SendChainPhaseEnv; simp only [hfpb]; exact he

end LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesBridge1PlacedBudget
