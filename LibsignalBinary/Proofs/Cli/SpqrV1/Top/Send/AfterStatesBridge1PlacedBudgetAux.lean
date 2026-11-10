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
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesChainPlacedBudget
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
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesChainStepPlacedBudget
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice

/-!
# Budget-Threaded `spqr::send` Phase 3b–3c Auxiliary Combinators and Envelopes

Defines the Phase 3b–3c allocator event envelopes, error cleanup steps, and `+3420..+4000`
chain step composition for `spqr::send::<signal_session_ratchet::Coins>`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesBridge1PlacedBudgetAux

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
open CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation (chainErrorAt)
open CryptoVerification.Cli.SpqrV1.Drop (chunkedStatesLocal1JumpTablePlacedAt)
open CryptoVerification.Cli.SpqrV1.Top.Send
  (call_lscro_calleeStack_anyPanic of_sepWP_lscro_b1 panic_lscro_calleeStack_anyPanic
   sendChainTargetPCPlaced spqrSendPlacedEntry spqrSendPlacedProg)
open CryptoVerification.SpqrV1.Top.Send
  (chainAt_entails_links_grow_ok optChainPBRegSlotAt optEpochSecretRegSlotAt
   pure_elim_focus_b1 sendKeyIntoPbChain sendStepChain spqrSendCalleeStack)
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
open LibsignalBinary.Proofs.SpqrV1.Top.ChainFrom.DefsBudget (ChainFromVersionNegotiationEnv)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesChainPlacedBudget
  (DeallocOkPlaced step_drop_key_31784_placed step_err_31764_placed step_err_31794_placed)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesChainResolvePlacedBudget
  (step_branch_key_none_315b8_placed step_branch_key_some_315b8_placed
   step_from_vn_none_3164c_placed step_post_from_pb_err_31510_placed
   step_post_from_vn_err_31674_placed step_post_send_key_err_315f4_placed
   step_post_send_key_ok_315f4_placed step_pre_add_epoch_315bc_placed
   step_pre_send_key_315dc_placed)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesChainStepPlacedBudget
  (step_err_31600_placed step_post_chain_into_pb_31734_placed step_pre_chain_into_pb_316dc_placed)

variable [LibsignalPlacement]

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnAddr Program.fnOff Obj.lookup

/-- Definitional equality bridge between `States1aPlacedBudget.dropChunkedStatesLocal1PlacedSpec` and
    `AfterStatesChainPlacedBudget.dropChunkedStatesLocal1PlacedSpec`. -/
theorem dropChunkedStatesLocal1PlacedSpec_eq (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (F : ShaCompress) :
    dropChunkedStatesLocal1PlacedSpec M A lim F =
      AfterStatesChainPlacedBudget.dropChunkedStatesLocal1PlacedSpec M A lim F := rfl

/-! ## 1. `LibsignalCodeRoLoaded` Budget Call & Step Combinators -/

private theorem stackAt_callee_split (sp : BitVec 64) (n : Nat)
    (hle : n ≤ spqrSendCalleeStack := by decide) :
    stackAt sp spqrSendCalleeStack =
      memRegion (sp - BitVec.ofNat 64 spqrSendCalleeStack) (spqrSendCalleeStack - n) ∗
        stackAt sp n := by
  have hle' : n ≤ 123008 := hle
  have hbd : n + (spqrSendCalleeStack - n) ≤ 2 ^ 64 := by change n + (123008 - n) ≤ 2 ^ 64; omega
  have h := ProofLib.stackAt_split_bottom sp n (spqrSendCalleeStack - n) hbd
  rwa [Nat.add_sub_of_le hle] at h

private theorem panic_frame_anyHeap {m : Memory} {φ₁ φ₂ : Prop} {F Fr : SepProp}
    (himp : φ₁ → φ₂) (hm : m ⊨ ((⌜φ₁⌝ ∗ anyHeap) ∗ F) ∗ Fr) :
    m ⊨ (⌜φ₂⌝ ∗ anyHeap) ∗ Fr := by
  have h1 : ((⌜φ₁⌝ ∗ anyHeap) ∗ F) ∗ Fr ⊢ ⌜φ₁⌝ ∗ ((anyHeap ∗ F) ∗ Fr) := Entails.of_eq (by sep_ac_rfl)
  have hm' := Satisfies.mono h1 hm; rw [satisfies_pure_sepConj] at hm'
  exact Satisfies.mono (sepConj_mono_left (Entails.pure_right (himp hm'.1) (entails_anyHeap _))) hm'.2

private theorem panic_not_exited {m : Memory} {R : SepProp} (h : m ⊨ ⌜False⌝ ∗ R) : False :=
  ((satisfies_pure_sepConj _ _ _).mp h).1

/-- Variant of `call_lscro_calleeStack_anyPanic` that unpacks an existential `evs : List AllocEvent`
    from `spec.post`. -/
theorem call_lscro_calleeStack_evs_anyPanic {α : Type} {prog : Program}
    {entry ret_pc ret : BitVec 64} {spec : Spec α} {x : α} {s : State}
    (sp : BitVec 64) (n : Nat) (hle : n ≤ spqrSendCalleeStack := by decide)
    {P T_pre : SepProp} {T_post : List AllocEvent → State → SepProp}
    {Q : State → SepProp → Prop} {Fr F : SepProp}
    {φ_pre : Prop} {φ_post : List AllocEvent → State → Prop} {φ_pan φ_out : State → Prop}
    (hcall : subroutine_ok prog entry (withLsCodeRoLoaded lsmpl spec))
    (hinv : LibsignalCodeRoLoaded lsmpl s.mem) (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hsp_align : (sp &&& 15#64 == 0#64) = true) (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec_pre : spec.pre x s = (⌜φ_pre⌝ ∗ T_pre ∗ stackAt s.sp n)) (hφ : φ_pre)
    (hP : P = (stackAt sp spqrSendCalleeStack ∗ T_pre) ∗ F)
    (hexit_eq : ∀ code sf, spec.onExit x code s sf = ⌜False⌝)
    (hpan_eq : ∀ sf, spec.onPanic x s sf = (⌜φ_pan sf⌝ ∗ anyHeap)) (hpan_imp : ∀ sm : State, φ_pan sm → φ_out sm)
    (hspec_post : ∀ sf, spec.post x s sf =
      (∃∗ evs : List AllocEvent, ⌜φ_post evs sf⌝ ∗ T_post evs sf ∗ stackAt s.sp n))
    (hnext : ∀ (evs : List AllocEvent) (sf : State),
      sf.pc = ret_pc → sf.status = .Running → sf.sp = sp → φ_post evs sf → LibsignalCodeRoLoaded lsmpl sf.mem →
      sf.readReg64 .x19 = s.readReg64 .x19 → sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x21 = s.readReg64 .x21 → sf.readReg64 .x22 = s.readReg64 .x22 →
      sf.readReg64 .x23 = s.readReg64 .x23 → sf.readReg64 .x24 = s.readReg64 .x24 →
      sf.readReg64 .x25 = s.readReg64 .x25 → sf.readReg64 .x26 = s.readReg64 .x26 →
      sf.readReg64 .x27 = s.readReg64 .x27 → sf.readReg64 .x28 = s.readReg64 .x28 →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWPp prog ret sf ((stackAt sp spqrSendCalleeStack ∗ T_post evs sf) ∗ F) Q
        (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ (⌜φ_out sf⌝ ∗ anyHeap) ∗ Fr)))
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    SepWPp prog ret s P Q (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ (⌜φ_out sf⌝ ∗ anyHeap) ∗ Fr)) := by
  let F_ext := memRegion (sp - BitVec.ofNat 64 spqrSendCalleeStack) (spqrSendCalleeStack - n) ∗ F
  have hsp_al : s.spAligned = true := by unfold State.spAligned; rw [hsp]; exact hsp_align
  have hwpp : SepWPp prog ret_pc s P
      (fun sm Pm => sm.sp = s.sp ∧ CalleeSavedPreserved s sm ∧ Pm = (withLsCodeRoLoaded lsmpl spec).post x s sm ∗ F_ext)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ (⌜φ_out sf⌝ ∗ anyHeap) ∗ Fr)) := by
    refine SepWPp.call (x := x) (F := F_ext) hcall hpc hrun hsp_al hlr ?_ ?_ ?_ ?_ ?_
    · intro R' hm
      change s.mem ⊨ (spec.pre x s ∗ ⌜LibsignalCodeRoLoaded lsmpl s.mem⌝) ∗ (F_ext ∗ R')
      rw [sepConj_comm (spec.pre x s), sepConj_assoc, satisfies_pure_sepConj]; refine ⟨hinv, ?_⟩
      rw [hspec_pre, hsp, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]; refine ⟨hφ, ?_⟩
      rw [hP, stackAt_callee_split sp n hle] at hm
      exact Satisfies.mono (Entails.of_eq (by dsimp only [F_ext]; sep_ac_rfl)) hm
    · intro sm code R' _ hpost
      change sm.mem ⊨ spec.onExit x code s sm ∗ R' at hpost
      rw [hexit_eq code sm] at hpost; exact panic_not_exited hpost
    · intro sm _ hmFr
      change sm.mem ⊨ (spec.onPanic x s sm ∗ F_ext) ∗ Fr at hmFr
      rw [hpan_eq sm] at hmFr; exact panic_frame_anyHeap (hpan_imp sm) hmFr
    · intro sm hpcm hrunm hspm hcsm; exact SepWPp.done hpcm hrunm ⟨hspm, hcsm, rfl⟩
    · intro sm R' _ hpost
      change sm.mem ⊨ spec.onOom x s sm ∗ (F_ext ∗ R') at hpost
      rw [hoom_eq sm] at hpost; exact (panic_not_exited hpost).elim
  intro R' hm hL
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, _, hpost, hspm, hcsm, rfl⟩ | hpan_or_oom⟩ := hwpp R' hm hL
  · change sm.mem ⊨ (spec.post x s sm ∗ F_ext) ∗ R' at hpost
    rw [sepConj_assoc, hspec_post sm, hsp, sepExists_sepConj_left] at hpost
    rcases (satisfies_sepExists _ _).mp hpost with ⟨evs, hpost⟩
    have hpost' : sm.mem ⊨ ⌜φ_post evs sm⌝ ∗
        (((stackAt sp spqrSendCalleeStack ∗ T_post evs sm) ∗ F) ∗ R') := by
      rw [stackAt_callee_split sp n hle]
      exact Satisfies.mono (Entails.of_eq (by dsimp only [F_ext]; sep_ac_rfl)) hpost
    rw [satisfies_pure_sepConj] at hpost'; rcases hpost' with ⟨hφ_post, hpost_mem⟩
    rw [hsp] at hspm
    rcases hcsm with ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, _, hvregs⟩
    obtain ⟨sf, hsteps', hout'⟩ := hnext evs sm hpcm hrunm hspm hφ_post
      (hinv.of_keepsFrozen hsteps.keepsFrozen)
      hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hvregs R' hpost_mem (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact ⟨sm, hsteps, Or.inr hpan_or_oom⟩

/-! ## 2. Error Paths (`+3252`, `+3608`, `+3568`, `+3480`) -/

abbrev step_panic_key_without_chain_317d8_placed :=
  @CryptoVerification.Cli.SpqrV1.Top.Send.step_panic_key_without_chain_317d8_placed

abbrev step_panic_epoch_zero_315dc_placed :=
  @CryptoVerification.Cli.SpqrV1.Top.Send.step_panic_epoch_zero_315dc_placed

theorem step_from_pb_err_31510_to_31a3c_placed {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc : DeallocOkPlaced M A lim ext)
    (hdrop_states : subroutine_ok (spqrSendPlacedProg ext)
      (lsmpl.base 443) (withLsCodeLoaded lsmpl (dropChunkedStatesLocal1PlacedSpec M A lim F)))
    (s : State) (st : M.σ) (ret x21 x27 x23 : BitVec 64) (err : Error)
    (st1 : States spqrPolyApi (spqrAuthApi F)) (key : Option EpochSecret) (Frame : SepProp)
    (hcl : LibsignalCodeLoaded lsmpl s.mem) (hpc : s.pc = spqrSendPlacedEntry + 3252#64)
    (hrun : s.status = .Running) (hx19 : s.readReg64 .x19 = ret)
    (hx21 : s.readReg64 .x21 = x21) (hx23 : s.readReg64 .x23 = x23)
    (hx26 : s.readReg64 .x26 = s.sp + 0x1260#64) (hx27 : s.readReg64 .x27 = x27)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) :
    SepWP (spqrSendPlacedProg ext) (spqrSendPlacedEntry + 4576#64) s
      (chainErrorAt (s.sp + 0x1260#64) err ∗ memRegion (s.sp + 0x1060#64) 24 ∗ memRegion ret 72 ∗
        chunkedStatesAt A.repAlloc (s.sp + 0x190#64) st1 ∗ optEpochSecretRegSlotAt A.repAlloc s.sp x21 x27 key ∗
        chunkedStatesLocal1JumpTablePlacedAt ∗ A.pool lim st s ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
      (fun sf Q => ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
        sf.status = .Running ∧ sf.trace = s.trace ∧ sf.sp = s.sp ∧ sf.readReg64 .x23 = x23 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (Q ⊢ spqrSendResultAt A.repAlloc ret none ∗ memRegion (s.sp + 0x1260#64) 88 ∗
          memRegion (s.sp + 0x1060#64) 24 ∗ memRegion (s.sp + 0x190#64) 928 ∗ memRegion (s.sp + 0x1bc0#64) 16 ∗
          chunkedStatesLocal1JumpTablePlacedAt ∗ A.pool lim (M.stepEvents evs st) sf ∗
          stackAt s.sp spqrSendCalleeStack ∗ Frame)) := by
  have hstep1 := step_post_from_pb_err_31510_placed (ext := ext) s err
    (memRegion ret 72 ∗ chunkedStatesAt A.repAlloc (s.sp + 0x190#64) st1 ∗
      optEpochSecretRegSlotAt A.repAlloc s.sp x21 x27 key ∗
      chunkedStatesLocal1JumpTablePlacedAt ∗ A.pool lim st s ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
    hpc hrun hx26 hsp_align
  refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) (sepWP_seq_lscl hcl (SepWP.mono hstep1 ?_))
  intro s1 P1 hpc1 _ ⟨hvm1, hrun1, htr1, hsp1, hx19_1, hx21_1, hx23_1, hx27_1, hvregs1, hP1⟩ hcl1
  have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by rw [hsp1]; exact hsp_align
  refine SepWP.weaken_pre hP1 ?_; wp_pull_exists; rename_i w1 w2 w3
  wp_conv_pre => rw [← A.pool_of_vmPreserved hvm1, ← hsp1]
  have hstep2 := step_err_31764_placed hdealloc hdrop_states s1 st ret x21 x27 x23 w1 w2 w3 st1 key
    (memRegion (s1.sp + 0x1260#64) 88 ∗ Frame)
    hcl1 hpc1 hrun1 (hx19_1.trans hx19) (hx21_1.trans hx21) (hx27_1.trans hx27) (hx23_1.trans hx23) hsp1_align
  refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) (SepWP.mono hstep2 ?_)
  intro sf Q _ _ ⟨evs, hevs, _, hrunf, htrf, hspf, hx23f, hvregsf, hQ⟩
  rw [hsp1] at hspf hQ
  exact ⟨evs, hevs, hrunf, htrf.trans htr1, hspf, hx23f, hvregsf.trans hvregs1,
    Entails.trans hQ (Entails.of_eq (by sep_ac_rfl))⟩

theorem step_from_vn_err_31674_to_31a3c_placed {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc : DeallocOkPlaced M A lim ext)
    (hdrop_states : subroutine_ok (spqrSendPlacedProg ext)
      (lsmpl.base 443) (withLsCodeLoaded lsmpl (dropChunkedStatesLocal1PlacedSpec M A lim F)))
    (s : State) (st : M.σ) (ret x21 x27 x23 : BitVec 64) (err : Error)
    (st1 : States spqrPolyApi (spqrAuthApi F)) (key : Option EpochSecret) (Frame : SepProp)
    (hcl : LibsignalCodeLoaded lsmpl s.mem) (hpc : s.pc = spqrSendPlacedEntry + 3608#64)
    (hrun : s.status = .Running) (hx19 : s.readReg64 .x19 = ret)
    (hx21 : s.readReg64 .x21 = x21) (hx23 : s.readReg64 .x23 = x23)
    (hx26 : s.readReg64 .x26 = s.sp + 0x1260#64) (hx27 : s.readReg64 .x27 = x27)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) :
    SepWP (spqrSendPlacedProg ext) (spqrSendPlacedEntry + 4576#64) s
      (chainErrorAt (s.sp + 0x1260#64) err ∗ memRegion (s.sp + 0x590#64) 24 ∗ memRegion ret 72 ∗
        chunkedStatesAt A.repAlloc (s.sp + 0x190#64) st1 ∗ optEpochSecretRegSlotAt A.repAlloc s.sp x21 x27 key ∗
        chunkedStatesLocal1JumpTablePlacedAt ∗ A.pool lim st s ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
      (fun sf Q => ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
        sf.status = .Running ∧ sf.trace = s.trace ∧ sf.sp = s.sp ∧ sf.readReg64 .x23 = x23 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (Q ⊢ spqrSendResultAt A.repAlloc ret none ∗ memRegion (s.sp + 0x1260#64) 88 ∗
          memRegion (s.sp + 0x590#64) 24 ∗ memRegion (s.sp + 0x190#64) 928 ∗ memRegion (s.sp + 0x1bc0#64) 16 ∗
          chunkedStatesLocal1JumpTablePlacedAt ∗ A.pool lim (M.stepEvents evs st) sf ∗
          stackAt s.sp spqrSendCalleeStack ∗ Frame)) := by
  have hstep1 := step_post_from_vn_err_31674_placed hdrop_states s st ret err st1
    (optEpochSecretRegSlotAt A.repAlloc s.sp x21 x27 key ∗ Frame) hcl hpc hrun hx19 hx26 hsp_align
  refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) (SepWP.seq hstep1 ?_)
  intro s1 P1 hpc1 _ ⟨evs₁, hevs₁, _, hrun1, htr1, hsp1, hx21_1, hx23_1, hx27_1, hvregs1, hP1⟩
  have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by rw [hsp1]; exact hsp_align
  refine SepWP.weaken_pre hP1 ?_; wp_conv_pre => rw [← hsp1]
  have hstep2 := step_drop_key_31784_placed hdealloc s1 (M.stepEvents evs₁ st) x21 x27 x23 key
    (spqrSendResultAt A.repAlloc ret none ∗ memRegion (s1.sp + 0x1260#64) 88 ∗
      memRegion (s1.sp + 0x590#64) 24 ∗ memRegion (s1.sp + 0x190#64) 928 ∗ chunkedStatesLocal1JumpTablePlacedAt ∗ Frame)
    hpc1 hrun1 (hx21_1.trans hx21) (hx27_1.trans hx27) (hx23_1.trans hx23) hsp1_align
  refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) (SepWP.mono hstep2 ?_)
  intro sf Q _ _ ⟨evs₂, hevs₂, _, hrunf, htrf, hspf, hx23f, hvregsf, hQ⟩
  rw [hsp1] at hspf hQ
  refine ⟨evs₁ ++ evs₂, FreeOnlyEvs.append hevs₁ hevs₂, hrunf, htrf.trans htr1, hspf, hx23f,
    hvregsf.trans hvregs1, ?_⟩
  rw [M.stepEvents_append]; exact Entails.trans hQ (Entails.of_eq (by sep_ac_rfl))

theorem step_vn_none_3164c_to_31a3c_placed {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc : DeallocOkPlaced M A lim ext)
    (hdrop_states : subroutine_ok (spqrSendPlacedProg ext)
      (lsmpl.base 443) (withLsCodeLoaded lsmpl (dropChunkedStatesLocal1PlacedSpec M A lim F)))
    (s : State) (st : M.σ) (ret x21 x27 x23 : BitVec 64)
    (st1 : States spqrPolyApi (spqrAuthApi F)) (key : Option EpochSecret) (Frame : SepProp)
    (hcl : LibsignalCodeLoaded lsmpl s.mem) (hpc : s.pc = spqrSendPlacedEntry + 3568#64)
    (hrun : s.status = .Running) (hx19 : s.readReg64 .x19 = ret)
    (hx21 : s.readReg64 .x21 = x21) (hx23 : s.readReg64 .x23 = x23)
    (hx27 : s.readReg64 .x27 = x27) (hsp_align : (s.sp &&& 15#64 == 0#64) = true) :
    SepWP (spqrSendPlacedProg ext) (spqrSendPlacedEntry + 4576#64) s
      (optVersionNegotiationPBAt A.repAlloc (s.sp + 0x30#64) none ∗ memRegion ret 72 ∗
        chunkedStatesAt A.repAlloc (s.sp + 0x190#64) st1 ∗ optEpochSecretRegSlotAt A.repAlloc s.sp x21 x27 key ∗
        chunkedStatesLocal1JumpTablePlacedAt ∗ A.pool lim st s ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
      (fun sf Q => ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
        sf.status = .Running ∧ sf.trace = s.trace ∧ sf.sp = s.sp ∧ sf.readReg64 .x23 = x23 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (Q ⊢ spqrSendResultAt A.repAlloc ret none ∗ optVersionNegotiationPBAt A.repAlloc (s.sp + 0x30#64) none ∗
          memRegion (s.sp + 0x190#64) 928 ∗ memRegion (s.sp + 0x1bc0#64) 16 ∗
          chunkedStatesLocal1JumpTablePlacedAt ∗ A.pool lim (M.stepEvents evs st) sf ∗
          stackAt s.sp spqrSendCalleeStack ∗ Frame)) := by
  have hstep1 := step_from_vn_none_3164c_placed (M := M) (A := A) (ext := ext) s
    (memRegion ret 72 ∗ chunkedStatesAt A.repAlloc (s.sp + 0x190#64) st1 ∗
      optEpochSecretRegSlotAt A.repAlloc s.sp x21 x27 key ∗
      chunkedStatesLocal1JumpTablePlacedAt ∗ A.pool lim st s ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
    hpc hrun hsp_align
  refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) (sepWP_seq_lscl hcl (SepWP.mono hstep1 ?_))
  intro s1 P1 hpc1 _ ⟨hvm1, hrun1, htr1, hsp1, hx19_1, hx21_1, hx23_1, hx27_1, hvregs1, hP1⟩ hcl1
  have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by rw [hsp1]; exact hsp_align
  refine SepWP.weaken_pre hP1 ?_; wp_conv_pre => rw [← A.pool_of_vmPreserved hvm1, ← hsp1]
  have hstep2 := step_err_31794_placed hdealloc hdrop_states s1 st ret x21 x27 x23 st1 key
    (optVersionNegotiationPBAt A.repAlloc (s1.sp + 0x30#64) none ∗ Frame)
    hcl1 hpc1 hrun1 (hx19_1.trans hx19) (hx21_1.trans hx21) (hx27_1.trans hx27) (hx23_1.trans hx23) hsp1_align
  refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) (SepWP.mono hstep2 ?_)
  intro sf Q _ _ ⟨evs, hevs, _, hrunf, htrf, hspf, hx23f, hvregsf, hQ⟩
  rw [hsp1] at hspf hQ
  exact ⟨evs, hevs, hrunf, htrf.trans htr1, hspf, hx23f, hvregsf.trans hvregs1,
    Entails.trans hQ (Entails.of_eq (by sep_ac_rfl))⟩

theorem step_send_key_err_315f4_to_31a3c_placed {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc : DeallocOkPlaced M A lim ext)
    (hdrop_slice : subroutine_ok (spqrSendPlacedProg ext)
      (lsmpl.base 446) (withLsCodeLoaded lsmpl (dropChainEpochSliceSpec M A lim)))
    (hdrop_states : subroutine_ok (spqrSendPlacedProg ext)
      (lsmpl.base 443) (withLsCodeLoaded lsmpl (dropChunkedStatesLocal1PlacedSpec M A lim F)))
    (s : State) (st : M.σ) (ret x23 : BitVec 64) (err : Error)
    (c : Chain) (st1 : States spqrPolyApi (spqrAuthApi F)) (Frame : SepProp)
    (hcl : LibsignalCodeLoaded lsmpl s.mem) (hpc : s.pc = spqrSendPlacedEntry + 3480#64)
    (hrun : s.status = .Running) (hx19 : s.readReg64 .x19 = ret)
    (hx23 : s.readReg64 .x23 = x23) (hsp_align : (s.sp &&& 15#64 == 0#64) = true) :
    SepWP (spqrSendPlacedProg ext) (spqrSendPlacedEntry + 4576#64) s
      (sendKeyErrAt (s.sp + 0x1260#64) err ∗ memRegion ret 72 ∗ chainRepr A.repAlloc (s.sp + 0x590#64) c ∗
        chunkedStatesAt A.repAlloc (s.sp + 0x190#64) st1 ∗ chunkedStatesLocal1JumpTablePlacedAt ∗
        A.pool lim st s ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
      (fun sf Q => ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
        sf.status = .Running ∧ sf.trace = s.trace ∧ sf.sp = s.sp ∧ sf.readReg64 .x23 = x23 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (Q ⊢ spqrSendResultAt A.repAlloc ret none ∗ memRegion (s.sp + 0x1260#64) 40 ∗
          memRegion (s.sp + 0x590#64) 88 ∗ memRegion (s.sp + 0x190#64) 928 ∗
          chunkedStatesLocal1JumpTablePlacedAt ∗ A.pool lim (M.stepEvents evs st) sf ∗
          stackAt s.sp spqrSendCalleeStack ∗ Frame)) := by
  have hstep1 := step_post_send_key_err_315f4_placed (ext := ext) s err
    (memRegion ret 72 ∗ chainRepr A.repAlloc (s.sp + 0x590#64) c ∗
      chunkedStatesAt A.repAlloc (s.sp + 0x190#64) st1 ∗
      chunkedStatesLocal1JumpTablePlacedAt ∗ A.pool lim st s ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
    hpc hrun hsp_align
  refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) (sepWP_seq_lscl hcl (SepWP.mono hstep1 ?_))
  intro s1 P1 hpc1 _ ⟨hvm1, hrun1, htr1, hsp1, hx19_1, _, _, _, hx23_1, _, _, _, _, hvregs1, hP1⟩ hcl1
  have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by rw [hsp1]; exact hsp_align
  refine SepWP.weaken_pre hP1 ?_; wp_pull_exists; rename_i d0 d1 w2 w3
  wp_conv_pre => rw [← A.pool_of_vmPreserved hvm1, ← hsp1]
  have hstep2 := step_err_31600_placed hdealloc hdrop_slice hdrop_states s1 st ret x23 1#64 d0 d1 w2 w3 c st1 Frame
    hcl1 hpc1 hrun1 (hx19_1.trans hx19) (hx23_1.trans hx23) hsp1_align
  refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) (SepWP.mono hstep2 ?_)
  intro sf Q _ _ ⟨evs, hevs, _, hrunf, htrf, hspf, hx23f, hvregsf, hQ⟩
  rw [hsp1] at hspf hQ
  exact ⟨evs, hevs, hrunf, htrf.trans htr1, hspf, hx23f, hvregsf.trans hvregs1,
    Entails.trans hQ (Entails.of_eq (by sep_ac_rfl))⟩

/-! ## 3. Phase 3b–3c Envelopes & Chain Step Composition (`+3420 -> +4000 / +4576 / panic`) -/

/-- Event envelope of the `<spqr::chain::Chain>::send_key` call inside `sendKeyIntoPbChain`. -/
def SendKeyFirstEnv (hkdf : HkdfFn) (c1 : Chain) (msgEpoch : Epoch)
    (evs : List AllocEvent) : Prop :=
  ∃ x : ChainSendKeyGhost,
    x.self = c1 ∧ x.epoch = msgEpoch - 1#64 ∧ ChainSendKeyAllocEnv hkdf x evs

/-- Event envelope of the `<spqr::chain::Chain>::into_pb` call on `c2`. -/
def ChainIntoPbForEnv (c2 : Chain) (evs : List AllocEvent) : Prop :=
  if c2.links = [] then
    FreeOnlyEvs evs
  else
    ∃ evs_free, FreeOnlyEvs evs_free ∧
      evs = rustAllocEvents (c2.links.length * 112) 8 ++ evs_free

/-- Relational allocator event envelope of `sendKeyIntoPbChain hkdf c1 msgEpoch`. -/
def SendKeyIntoPbEnv (hkdf : HkdfFn) (c1 : Chain) (msgEpoch : Epoch)
    (evs : List AllocEvent) : Prop :=
  if msgEpoch = 0#64 then
    evs = []
  else
    match Chain.sendKey hkdf c1 (msgEpoch - 1#64) with
    | .error _ => FreeOnlyEvs evs
    | .ok (c2, _, _) => SeqEnv (SendKeyFirstEnv hkdf c1 msgEpoch) (ChainIntoPbForEnv c2) evs

/-- Event envelope of the `<spqr::chain::Chain>::add_epoch` call inside `sendStepChain`. -/
def AddEpochFirstEnv (hkdf : HkdfFn) (c0 : Chain) (es : EpochSecret)
    (evs : List AllocEvent) : Prop :=
  ∃ x : ChainAddEpochGhost,
    x.self = c0 ∧ x.epochSecret = es ∧
    (x.self.links.length < x.G.linksCap.toNat ∨
      max (2 * x.G.linksCap.toNat) 4 * chainEpochSize < 2 ^ 63) ∧
    ChainAddEpochEnv hkdf x evs

/-- Relational allocator event envelope of `sendStepChain hkdf cOpt key msgEpoch`. -/
def SendStepChainEnv (hkdf : HkdfFn) (cOpt : Option Chain) (key : Option EpochSecret)
    (msgEpoch : Epoch) (evs : List AllocEvent) : Prop :=
  match cOpt, key with
  | none, none => evs = []
  | none, some _ => evs = []
  | some c0, none => SendKeyIntoPbEnv hkdf c0 msgEpoch evs
  | some c0, some es =>
    match Chain.addEpoch hkdf c0 es with
    | .error _ => evs = []
    | .ok c1 => SeqEnv (AddEpochFirstEnv hkdf c0 es) (SendKeyIntoPbEnv hkdf c1 msgEpoch) evs

/-- Relational allocator event envelope of `sendChainPhase hkdf chain vn key msgEpoch`. -/
def SendChainPhaseEnv (hkdf : HkdfFn) (chain : Option ChainPB)
    (vn : Option VersionNegotiationPB) (key : Option EpochSecret) (msgEpoch : Epoch)
    (evs : List AllocEvent) : Prop :=
  match chain with
  | some pb =>
    match Chain.fromPb pb with
    | .error _ => FreeOnlyEvs evs
    | .ok c0 => SeqEnv FreeOnlyEvs (SendStepChainEnv hkdf (some c0) key msgEpoch) evs
  | none =>
    match vn with
    | none => FreeOnlyEvs evs
    | some v =>
      if BitVec.slt 0#32 v.minVersion = true then
        match chainFromVersionNegotiation hkdf v with
        | .error _ => SeqEnv (ChainFromVersionNegotiationEnv v) FreeOnlyEvs evs
        | .ok c0 =>
          SeqEnv (ChainFromVersionNegotiationEnv v)
            (SendStepChainEnv hkdf (some c0) key msgEpoch) evs
      else
        SendStepChainEnv hkdf none key msgEpoch evs

/-- Budget-threaded postcondition of `sendChainPhase` / `sendStepChain` / `sendKeyIntoPbChain`
    at `+4000` (`.ok`) or `+4576` (`.error (.err _)`), parameterized by event envelope `Env`. -/
def sendChainPostPlaced {M : AllocCostModel} {F : ShaCompress}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (Env : List AllocEvent → Prop)
    (s0 : State) (sp ret x23 : BitVec 64) (st1 : States spqrPolyApi (spqrAuthApi F)) (Frame : SepProp)
    (res : SpqrApiResult (BitVec 32 × Bytes × Option ChainPB)) (sf : State) (Q : SepProp) : Prop :=
  match res with
  | .ok (idx, msgKey, chainPb) =>
    ∃ evs : List AllocEvent, Env evs ∧
      sf.status = .Running ∧ sf.trace = s0.trace ∧ sf.sp = sp ∧ LibsignalCodeRoLoaded lsmpl sf.mem ∧
      sf.readReg64 .x19 = ret ∧ sf.readReg64 .x22 = BitVec.ofNat 64 msgKey.length ∧
      sf.readReg64 .x23 = x23 ∧ sf.readReg32 .x24 = idx ∧ sf.readReg64 .x26 = sp + 0x1260#64 ∧
      sf.readReg64 .x28 = sp + 0x1060#64 ∧ (sf.readReg64 .x21 = noneCap ∨ sf.readReg32 .x20 = 0#32) ∧
      calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
      (Q ⊢ optChainPBRegSlotAt A.repAlloc (sp + 0xd90#64) (sf.readReg64 .x25) chainPb ∗
        (∃∗ mkCap : BitVec 64, ∃∗ mkPtr : BitVec 64,
          ((sp + 0x28#64) ↦₆₄ mkCap) ∗ ((sp + 0x8#64) ↦₆₄ mkPtr) ∗ vecU8Heap A.repAlloc mkCap mkPtr msgKey) ∗
        memRegion (sp + 0x590#64) 88 ∗ memRegion (sp + 0x1260#64) 88 ∗ memRegion (sp + 0x1060#64) 80 ∗
        memRegion ret 72 ∗ chunkedStatesAt A.repAlloc (sp + 0x190#64) st1 ∗ chunkedStatesLocal1JumpTablePlacedAt ∗
        A.pool lim (M.stepEvents evs st) sf ∗ stackAt sp spqrSendCalleeStack ∗ Frame)
  | .error (.err _) =>
    ∃ evs : List AllocEvent, Env evs ∧
      sf.status = .Running ∧ sf.trace = s0.trace ∧ sf.sp = sp ∧ LibsignalCodeRoLoaded lsmpl sf.mem ∧
      sf.readReg64 .x23 = x23 ∧ calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
      (Q ⊢ spqrSendResultAt A.repAlloc ret none ∗ memRegion (sp + 0x590#64) 88 ∗
        memRegion (sp + 0x1260#64) 88 ∗ memRegion (sp + 0x1060#64) 80 ∗ memRegion (sp + 0xd90#64) 72 ∗
        memRegion (sp + 0x28#64) 8 ∗ memRegion (sp + 0x8#64) 8 ∗ memRegion (sp + 0x190#64) 928 ∗
        chunkedStatesLocal1JumpTablePlacedAt ∗ A.pool lim (M.stepEvents evs st) sf ∗
        stackAt sp spqrSendCalleeStack ∗ Frame)
  | .error (.panic _) => False

theorem sendChainPostPlaced_mono {M : AllocCostModel} {F : ShaCompress}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {Env₁ Env₂ : List AllocEvent → Prop} (himp : ∀ evs, Env₁ evs → Env₂ evs)
    {s0 : State} {sp ret x23 : BitVec 64} {st1 : States spqrPolyApi (spqrAuthApi F)}
    {Frame : SepProp} {res : SpqrApiResult (BitVec 32 × Bytes × Option ChainPB)} {sf : State} {Q : SepProp}
    (h : sendChainPostPlaced A lim st Env₁ s0 sp ret x23 st1 Frame res sf Q) :
    sendChainPostPlaced A lim st Env₂ s0 sp ret x23 st1 Frame res sf Q := by
  cases res with
  | ok val => rcases val with ⟨idx, msgKey, chainPb⟩; rcases h with ⟨evs, hevs, hrest⟩; exact ⟨evs, himp evs hevs, hrest⟩
  | error e =>
    cases e with
    | err _ => rcases h with ⟨evs, hevs, hrest⟩; exact ⟨evs, himp evs hevs, hrest⟩
    | panic _ => exact False.elim h

theorem sendChainPostPlaced_step {M : AllocCostModel} {F : ShaCompress}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {E₁ E₂ : List AllocEvent → Prop} {evs₁ : List AllocEvent} (h1 : E₁ evs₁)
    {s0 : State} {sp ret x23 : BitVec 64} {st1 : States spqrPolyApi (spqrAuthApi F)}
    {Frame : SepProp} {res : SpqrApiResult (BitVec 32 × Bytes × Option ChainPB)} {sf : State} {Q : SepProp}
    (h : sendChainPostPlaced A lim (M.stepEvents evs₁ st) E₂ s0 sp ret x23 st1 Frame res sf Q) :
    sendChainPostPlaced A lim st (SeqEnv E₁ E₂) s0 sp ret x23 st1 Frame res sf Q := by
  cases res with
  | ok val =>
    rcases val with ⟨idx, msgKey, chainPb⟩
    rcases h with ⟨evs₂, h2, hrun, htr, hsp, hinv, hx19, hx22, hx23, hx24, hx26, hx28, hfl, hvr, hQ⟩
    refine ⟨evs₁ ++ evs₂, SeqEnv.append h1 h2, hrun, htr, hsp, hinv, hx19, hx22, hx23, hx24, hx26, hx28, hfl, hvr, ?_⟩
    rwa [M.stepEvents_append]
  | error e =>
    cases e with
    | err _ =>
      rcases h with ⟨evs₂, h2, hrun, htr, hsp, hinv, hx23, hvr, hQ⟩
      refine ⟨evs₁ ++ evs₂, SeqEnv.append h1 h2, hrun, htr, hsp, hinv, hx23, hvr, ?_⟩; rwa [M.stepEvents_append]
    | panic _ => exact False.elim h

theorem sepWPp_mono_post {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp}
    {Q₁ Q₂ Qp : State → SepProp → Prop} (himp : ∀ sf Pf, Q₁ sf Pf → Q₂ sf Pf)
    (h : SepWPp prog ret s P Q₁ Qp) : SepWPp prog ret s P Q₂ Qp := by
  intro R hm hL; obtain ⟨sf, hsteps, ⟨hpc, hrun, Pf, hPf, hQ1⟩ | hp⟩ := h R hm hL
  · exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, Pf, hPf, himp sf Pf hQ1⟩⟩
  · exact ⟨sf, hsteps, Or.inr hp⟩

private theorem readReg32_of_readReg64_eq {s1 s2 : State} {r : Reg} (h : s1.readReg64 r = s2.readReg64 r) :
    s1.readReg32 r = s2.readReg32 r := by unfold State.readReg32; rw [h]

private theorem flag_preserve {s1 s2 : State} (h : s1.readReg64 .x21 = noneCap ∨ s1.readReg32 .x20 = 0#32)
    (hx20 : s2.readReg64 .x20 = s1.readReg64 .x20) (hx21 : s2.readReg64 .x21 = s1.readReg64 .x21) :
    s2.readReg64 .x21 = noneCap ∨ s2.readReg32 .x20 = 0#32 :=
  h.imp (hx21.trans ·) ((readReg32_of_readReg64_eq hx20).trans ·)

theorem flag_of_csinc_315b8 {s : State} {x21 : BitVec 64} (hx21 : s.readReg64 .x21 = x21)
    (hx20 : s.readReg32 .x20 = (if (x21 + 1#64 != 0#64) = true then 0#32 else 1#32)) :
    s.readReg64 .x21 = noneCap ∨ s.readReg32 .x20 = 0#32 := by
  by_cases h : x21 = noneCap
  · exact Or.inl (hx21.trans h)
  · refine Or.inr (hx20.trans ?_)
    have hne : (x21 + 1#64 != 0#64) = true := by
      unfold noneCap at h; simp only [bne_iff_ne, ne_eq]; intro h0; apply h; bv_omega
    simp [hne]

private theorem memRegion_1260_88_eq_32_56 (sp : BitVec 64) :
    memRegion (sp + 0x1260#64) 88 = memRegion (sp + 0x1260#64) 32 ∗ memRegion (sp + 0x1280#64) 56 :=
  ProofLib.memRegion_split' (b := sp + 0x1260#64) (n := 32) (k := 56) (b' := sp + 0x1280#64) rfl (by bv_omega) (by decide)

private theorem memRegion_1260_88_eq_40_48 (sp : BitVec 64) :
    memRegion (sp + 0x1260#64) 88 = memRegion (sp + 0x1260#64) 40 ∗ memRegion (sp + 0x1288#64) 48 :=
  ProofLib.memRegion_split' (b := sp + 0x1260#64) (n := 40) (k := 48) (b' := sp + 0x1288#64) rfl (by bv_omega) (by decide)

theorem memRegion_590_88_eq_80_8 (sp : BitVec 64) :
    memRegion (sp + 0x590#64) 88 = memRegion (sp + 0x590#64) 80 ∗ memRegion (sp + 0x5e0#64) 8 :=
  ProofLib.memRegion_split' (b := sp + 0x590#64) (n := 80) (k := 8) (b' := sp + 0x5e0#64) rfl (by bv_omega) (by decide)

theorem memRegion_590_88_eq_24_64 (sp : BitVec 64) :
    memRegion (sp + 0x590#64) 88 = memRegion (sp + 0x590#64) 24 ∗ memRegion (sp + 0x5a8#64) 64 :=
  ProofLib.memRegion_split' (b := sp + 0x590#64) (n := 24) (k := 64) (b' := sp + 0x5a8#64) rfl (by bv_omega) (by decide)

theorem memRegion_1060_80_eq_24_56 (sp : BitVec 64) :
    memRegion (sp + 0x1060#64) 80 = memRegion (sp + 0x1060#64) 24 ∗ memRegion (sp + 0x1078#64) 56 :=
  ProofLib.memRegion_split' (b := sp + 0x1060#64) (n := 24) (k := 56) (b' := sp + 0x1078#64) rfl (by bv_omega) (by decide)

theorem step_chain_5dc_to_7fc_placed {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {F : ShaCompress} (hkdf : HkdfFn) {ext : String → Option (State → State)}
    (hpanic_sub : ext "_RNvNtNtCskxtBwYRO61I_4core9panicking11panic_const24panic_const_sub_overflow" = some Rust.panicked)
    (hdealloc : DeallocOkPlaced M A lim ext)
    (hdrop_slice : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 446) (withLsCodeLoaded lsmpl (dropChainEpochSliceSpec M A lim)))
    (hdrop_states : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 443) (withLsCodeLoaded lsmpl (dropChunkedStatesLocal1PlacedSpec M A lim F)))
    (hsend_key : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 367) (withLsCodeRoLoaded lsmpl (chainSendKeySpecX hkdf M A lim)))
    (hinto_pb : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 365) (withLsCodeRoLoaded lsmpl (chainIntoPbSpecX M A lim)))
    (s0 s : State) (st : M.σ) (ret x23 : BitVec 64) (c1 : Chain) (msgEpoch : Epoch)
    (st1 : States spqrPolyApi (spqrAuthApi F)) (Frame Fr : SepProp) (φ_out : State → Prop)
    (hFit : FitsEnv M lim st (SendKeyIntoPbEnv hkdf c1 msgEpoch))
    (hinv : LibsignalCodeRoLoaded lsmpl s.mem) (hpc : s.pc = spqrSendPlacedEntry + 3456#64)
    (hrun : s.status = .Running) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = ret) (hx22 : s.readReg64 .x22 = msgEpoch)
    (hx23 : s.readReg64 .x23 = x23) (hx26 : s.readReg64 .x26 = s.sp + 0x1260#64)
    (hx28 : s.readReg64 .x28 = s.sp + 0x1060#64)
    (hflag : s.readReg64 .x21 = noneCap ∨ s.readReg32 .x20 = 0#32)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hφ : ∀ sf : State, (sendKeyIntoPbChain hkdf c1 msgEpoch).isPanic = true ∧ sf.trace = s0.trace → φ_out sf)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0 := by simp only [wp_norm, arm64_norm, *]) :
    SepWPp (spqrSendPlacedProg ext) (sendChainTargetPCPlaced (sendKeyIntoPbChain hkdf c1 msgEpoch)) s
      (chainRepr A.repAlloc (s.sp + 0x590#64) c1 ∗ memRegion (s.sp + 0x1260#64) 88 ∗
        memRegion (s.sp + 0x1060#64) 80 ∗ memRegion (s.sp + 0xd90#64) 72 ∗ memRegion (s.sp + 0x28#64) 8 ∗
        memRegion (s.sp + 0x8#64) 8 ∗ memRegion ret 72 ∗ chunkedStatesAt A.repAlloc (s.sp + 0x190#64) st1 ∗
        chunkedStatesLocal1JumpTablePlacedAt ∗ A.pool lim st s ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
      (sendChainPostPlaced A lim st (SendKeyIntoPbEnv hkdf c1 msgEpoch) s0 s.sp ret x23 st1 Frame
        (sendKeyIntoPbChain hkdf c1 msgEpoch))
      (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ (⌜φ_out sf⌝ ∗ anyHeap) ∗ Fr)) := by
  by_cases hep0 : msgEpoch = 0#64
  · refine step_panic_epoch_zero_315dc_placed ext hpanic_sub hinv hpc hrun (hx22.trans hep0) fun sf htr_f => ?_
    exact hφ sf ⟨by unfold sendKeyIntoPbChain; simp [hep0]; rfl, htr_f.trans htr⟩
  · have hep0_beq : (msgEpoch == 0#64) = false := beq_eq_false_iff_ne.mpr hep0
    have hpre_sk := step_pre_send_key_315dc_placed (ext := ext) s
      (chainRepr A.repAlloc (s.sp + 0x590#64) c1 ∗ memRegion (s.sp + 0x1260#64) 88 ∗
        memRegion (s.sp + 0x1060#64) 80 ∗ memRegion (s.sp + 0xd90#64) 72 ∗ memRegion (s.sp + 0x28#64) 8 ∗
        memRegion (s.sp + 0x8#64) 8 ∗ memRegion ret 72 ∗ chunkedStatesAt A.repAlloc (s.sp + 0x190#64) st1 ∗
        chunkedStatesLocal1JumpTablePlacedAt ∗ A.pool lim st s ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
      hpc hrun (by rw [hx22]; exact hep0)
    apply of_sepWP_lscro_b1 (mid := lsmpl.base 367) hinv
    refine SepWP.mono hpre_sk ?_
    rintro s1 P1 hpc1 hrun1 ⟨hvm1, _, htr1, hsp1, hx8_1, hx0_1, hx1_1, hx30_1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, _, _, hx26_1, _, hx28_1, hvregs1, rfl⟩ hinv1
    rw [← A.pool_of_vmPreserved hvm1]; dsimp only [chainRepr]; rw [sepExists_sepConj_left]
    apply SepWPp.exists_elim; intro G; rw [memRegion_1260_88_eq_40_48 s.sp]
    let x_sk : ChainSendKeyGhost := ⟨s.sp + 0x1260#64, s.sp + 0x590#64, msgEpoch - 1#64, G, c1⟩
    have hFit_sk : FitsEnv M lim st (ChainSendKeyAllocEnv hkdf x_sk) := by
      cases hsk_fit : Chain.sendKey hkdf c1 (msgEpoch - 1#64) with
      | error _ => intro evs hevs; dsimp only [ChainSendKeyAllocEnv, x_sk] at hevs; rw [hsk_fit] at hevs; subst hevs; trivial
      | ok val =>
        rcases val with ⟨c2, _, _⟩
        have hFit' : FitsEnv M lim st (SeqEnv (SendKeyFirstEnv hkdf c1 msgEpoch) (ChainIntoPbForEnv c2)) :=
          FitsEnv.mono (fun evs he => by unfold SendKeyIntoPbEnv; simp only [hep0, ↓reduceIte, hsk_fit]; exact he) hFit
        exact FitsEnv.mono (fun evs he => ⟨x_sk, rfl, rfl, he⟩) hFit'.seq_left
    refine call_lscro_calleeStack_evs_anyPanic (s.sp) chainSendKeyStackX (by decide) (x := (x_sk, st))
      (T_pre := memRegion (s.sp + 0x1260#64) 40 ∗ chainAt A.repAlloc (s.sp + 0x590#64) G c1 ∗ A.pool lim st s1)
      (T_post := fun evs₁ sf => sendKeyPostAt A.repAlloc (s.sp + 0x590#64) (s.sp + 0x1260#64) c1
        (Chain.sendKey hkdf c1 (msgEpoch - 1#64)) ∗ A.pool lim (M.stepEvents evs₁ st) sf)
      (F := memRegion (s.sp + 0x1288#64) 48 ∗ memRegion (s.sp + 0x1060#64) 80 ∗ memRegion (s.sp + 0xd90#64) 72 ∗
        memRegion (s.sp + 0x28#64) 8 ∗ memRegion (s.sp + 0x8#64) 8 ∗ memRegion ret 72 ∗
        chunkedStatesAt A.repAlloc (s.sp + 0x190#64) st1 ∗ chunkedStatesLocal1JumpTablePlacedAt ∗ Frame)
      (φ_pre := s1.readReg64 .x0 = x_sk.selfPtr ∧ s1.readReg64 .x1 = x_sk.epoch ∧ s1.readReg64 .x8 = x_sk.out ∧
        FitsEnv M lim st (ChainSendKeyAllocEnv hkdf x_sk))
      (φ_post := fun evs₁ sf => ChainSendKeyAllocEnv hkdf x_sk evs₁ ∧ sf.trace = s1.trace ∧ AllocCallPreserved s1 sf)
      hsend_key hinv1 hpc1 hrun1 hsp1 hsp_align hx30_1 (by dsimp only [chainSendKeySpecX, x_sk]; sep_ac_rfl)
      ⟨hx0_1, hx1_1.trans (congrArg (· - 1#64) hx22), hx8_1, hFit_sk⟩ (by sep_ac_rfl) (fun _ _ => rfl) (fun _ => rfl)
      (fun sm ⟨hpan_sk, htr_sm⟩ => by
        refine hφ sm ⟨?_, htr_sm.trans (htr1.trans htr)⟩
        unfold sendKeyIntoPbChain; simp only [hep0_beq, Bool.false_eq_true, ↓reduceIte]
        cases h : Chain.sendKey hkdf c1 (msgEpoch - 1#64) with
        | ok _ => dsimp only [x_sk] at hpan_sk; rw [h] at hpan_sk; contradiction
        | error e =>
          cases e with
          | err _ => dsimp only [x_sk] at hpan_sk; rw [h] at hpan_sk; contradiction
          | panic _ => rfl)
      (fun sf => by dsimp only [chainSendKeySpecX, x_sk]; exact congrArg sepExists (funext fun _ => by sep_ac_rfl)) ?_
    intro evs₁ s2 hpc2 hrun2 hsp2 ⟨h_sk1, htr2, _⟩ hinv2 hx19_2 hx20_2 hx21_2 _ hx23_2 _ _ hx26_2 _ hx28_2 hvregs2
    have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2]; exact hsp_align
    have htr2_0 : s2.trace = s0.trace := htr2.trans (htr1.trans htr)
    have hvregs2_0 : calleeSavedVRegs s2 = calleeSavedVRegs s0 := hvregs2.trans (hvregs1.trans hvregs)
    have hx19_20 : s2.readReg64 .x19 = ret := hx19_2.trans (hx19_1.trans hx19)
    have hx23_20 : s2.readReg64 .x23 = x23 := hx23_2.trans (hx23_1.trans hx23)
    have hx26_20 : s2.readReg64 .x26 = s.sp + 0x1260#64 := hx26_2.trans (hx26_1.trans hx26)
    have hx28_20 : s2.readReg64 .x28 = s.sp + 0x1060#64 := hx28_2.trans (hx28_1.trans hx28)
    have hflag2 := flag_preserve (flag_preserve hflag hx20_1 hx21_1) hx20_2 hx21_2
    cases hsk : Chain.sendKey hkdf c1 (msgEpoch - 1#64) with
    | error e =>
      cases e with
      | panic p => dsimp only [sendKeyPostAt]; exact pure_elim_focus_b1 False (fun h => h.elim)
      | err err =>
        have hevs1_nil : evs₁ = [] := by dsimp only [ChainSendKeyAllocEnv, x_sk] at h_sk1; rwa [hsk] at h_sk1
        subst hevs1_nil; simp only [M.stepEvents_nil]
        have hres : sendKeyIntoPbChain hkdf c1 msgEpoch = .error (.err err) := by
          unfold sendKeyIntoPbChain; simp [hep0_beq, hsk]; rfl
        rw [hres]; dsimp only [sendChainTargetPCPlaced, sendChainPostPlaced, sendKeyPostAt]
        apply of_sepWP_lscro_b1 (mid := spqrSendPlacedEntry + 4576#64) hinv2
        have herr_step := step_send_key_err_315f4_to_31a3c_placed hdealloc hdrop_slice hdrop_states
          s2 st ret x23 err c1 st1
          (memRegion (s.sp + 0x1288#64) 48 ∗ memRegion (s.sp + 0x1060#64) 80 ∗ memRegion (s.sp + 0xd90#64) 72 ∗
            memRegion (s.sp + 0x28#64) 8 ∗ memRegion (s.sp + 0x8#64) 8 ∗ Frame)
          hinv2.1 hpc2 hrun2 hx19_20 hx23_20 hsp2_align
        rw [hsp2] at herr_step
        refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) (SepWP.mono herr_step ?_)
        rintro sf Q hpcf hrunf ⟨evs₂, hevs₂, _, htrf, hspf, hx23f, hvregsf, hQ⟩ hinvf
        have hEnv_err : SendKeyIntoPbEnv hkdf c1 msgEpoch evs₂ := by
          unfold SendKeyIntoPbEnv; simp only [hep0, ↓reduceIte, hsk]; exact hevs₂
        refine SepWPp.done hpcf hrunf
          ⟨evs₂, hEnv_err, hrunf, htrf.trans htr2_0, hspf, hinvf, hx23f, hvregsf.trans hvregs2_0, ?_⟩
        rw [memRegion_1260_88_eq_40_48 s.sp]; exact Entails.trans hQ (Entails.of_eq (by sep_ac_rfl))
    | ok val =>
      rcases val with ⟨c2, idx, msgKey⟩
      have hres : sendKeyIntoPbChain hkdf c1 msgEpoch = .ok (idx, msgKey, some c2.intoPb) := by
        unfold sendKeyIntoPbChain; simp [hep0_beq, hsk]; rfl
      have h1_env : SendKeyFirstEnv hkdf c1 msgEpoch evs₁ := ⟨x_sk, rfl, rfl, h_sk1⟩
      have hFit_ipb_for : FitsEnv M lim (M.stepEvents evs₁ st) (ChainIntoPbForEnv c2) :=
        (FitsEnv.mono (fun evs he => by unfold SendKeyIntoPbEnv; simp only [hep0, ↓reduceIte, hsk]; exact he) hFit).seq_right h1_env
      rw [hres]; dsimp only [sendChainTargetPCPlaced, sendChainPostPlaced, sendKeyPostAt]
      have hok1 := step_post_send_key_ok_315f4_placed (M := M) (A := A) (ext := ext) s2 idx msgKey
        (chainRepr A.repAlloc (s.sp + 0x590#64) c2 ∗ memRegion (s.sp + 0x1288#64) 48 ∗
          memRegion (s.sp + 0x1060#64) 80 ∗ memRegion (s.sp + 0xd90#64) 72 ∗ memRegion (s.sp + 0x28#64) 8 ∗
          memRegion (s.sp + 0x8#64) 8 ∗ memRegion ret 72 ∗ chunkedStatesAt A.repAlloc (s.sp + 0x190#64) st1 ∗
          chunkedStatesLocal1JumpTablePlacedAt ∗ A.pool lim (M.stepEvents evs₁ st) s2 ∗
          stackAt s.sp spqrSendCalleeStack ∗ Frame)
        hpc2 hrun2 hsp2_align
      rw [hsp2] at hok1; apply of_sepWP_lscro_b1 (mid := spqrSendPlacedEntry + 3712#64) hinv2
      refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) (SepWP.mono hok1 ?_)
      rintro s3 P3 hpc3 hrun3 ⟨hvm3, _, htr3, hsp3, hx24_3, hx19_3, hx20_3, hx21_3, _, hx23_3, _, hx26_3, _, hx28_3, hvregs3, hP3⟩ hinv3
      refine SepWPp.weaken_pre hP3 ?_; rw [← A.pool_of_vmPreserved hvm3]
      have hsp3_align : (s3.sp &&& 15#64 == 0#64) = true := by rw [hsp3]; exact hsp_align
      have hok2 := step_pre_chain_into_pb_316dc_placed (M := M) (A := A) (ext := ext) s3 idx msgKey c2
        (memRegion (s.sp + 0x1060#64) 80 ∗ memRegion (s.sp + 0xd90#64) 72 ∗ memRegion ret 72 ∗
          chunkedStatesAt A.repAlloc (s.sp + 0x190#64) st1 ∗ chunkedStatesLocal1JumpTablePlacedAt ∗
          A.pool lim (M.stepEvents evs₁ st) s3 ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
        hpc3 hrun3 hsp3_align
      rw [hsp3] at hok2; apply of_sepWP_lscro_b1 (mid := lsmpl.base 365) hinv3
      refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) (SepWP.mono hok2 ?_)
      rintro s4 P4 hpc4 hrun4 ⟨hvm4, _, htr4, hsp4, hx0_4, hx8_4, hx30_4, hx22_4, hx19_4, hx20_4, hx21_4, hx23_4, hx24_4, hx26_4, _, hx28_4, hvregs4, hP4⟩ hinv4
      refine SepWPp.weaken_pre hP4 ?_; rw [← A.pool_of_vmPreserved hvm4]
      apply SepWPp.exists_elim; intro G2; apply SepWPp.exists_elim; intro mkCap; apply SepWPp.exists_elim; intro mkPtr
      have htr4_0 : s4.trace = s0.trace := htr4.trans (htr3.trans htr2_0)
      let x_ipb : ChainIntoPbCall := ⟨s.sp + 0x1060#64, s.sp + 0x1260#64, G2, c2⟩
      have hFit_ipb : FitsEnv M lim (M.stepEvents evs₁ st) (ChainIntoPbAllocEnv x_ipb) :=
        fitsEnv_chainIntoPbAllocEnv_of_chainIntoPbEnv hFit_ipb_for
      refine call_lscro_calleeStack_evs_anyPanic (s.sp) chainIntoPbStackX (by decide)
        (x := (x_ipb, M.stepEvents evs₁ st))
        (T_pre := memRegion (s.sp + 0x1060#64) 80 ∗ chainAt A.repAlloc (s.sp + 0x1260#64) G2 c2 ∗
          A.pool lim (M.stepEvents evs₁ st) s4)
        (T_post := fun evs₂ sf => protoChainPBAt A.repAlloc (s.sp + 0x1060#64) c2.intoPb ∗
          memRegion (s.sp + 0x1260#64) 88 ∗ A.pool lim (M.stepEvents evs₂ (M.stepEvents evs₁ st)) sf)
        (F := ((s.sp + 0x28#64) ↦₆₄ mkCap) ∗ ((s.sp + 0x8#64) ↦₆₄ mkPtr) ∗ vecU8Heap A.repAlloc mkCap mkPtr msgKey ∗
          memRegion (s.sp + 0x590#64) 88 ∗ memRegion (s.sp + 0xd90#64) 72 ∗ memRegion ret 72 ∗
          chunkedStatesAt A.repAlloc (s.sp + 0x190#64) st1 ∗ chunkedStatesLocal1JumpTablePlacedAt ∗ Frame)
        (φ_pre := s4.readReg64 .x8 = x_ipb.out ∧ s4.readReg64 .x0 = x_ipb.chainPtr ∧
          FitsEnv M lim (M.stepEvents evs₁ st) (ChainIntoPbAllocEnv x_ipb))
        (φ_post := fun evs₂ sf => ChainIntoPbEnv x_ipb evs₂ ∧ sf.trace = s4.trace ∧ AllocCallPreserved s4 sf)
        (φ_pan := fun _ => False) hinto_pb hinv4 hpc4 hrun4 hsp4 hsp_align hx30_4
        (by dsimp only [chainIntoPbSpecX, x_ipb]; sep_ac_rfl) ⟨hx8_4, hx0_4, hFit_ipb⟩
        (by sep_ac_rfl) (fun _ _ => rfl) (fun _ => by change ⌜False⌝ = _; symm; exact pure_false_sepConj _)
        (fun _ h => h.elim)
        (fun sf => by dsimp only [chainIntoPbSpecX, x_ipb]; exact congrArg sepExists (funext fun _ => by sep_ac_rfl)) ?_
      intro evs₂ s5 hpc5 hrun5 hsp5 ⟨h_ipb2, htr5, _⟩ hinv5 hx19_5 hx20_5 hx21_5 hx22_5 hx23_5 hx24_5 _ hx26_5 _ hx28_5 hvregs5
      have hsp5_align : (s5.sp &&& 15#64 == 0#64) = true := by rw [hsp5]; exact hsp_align
      have hx28_50 : s5.readReg64 .x28 = s5.sp + 0x1060#64 := by
        rw [hsp5]; exact hx28_5.trans (hx28_4.trans (hx28_3.trans hx28_20))
      have hflag5 := flag_preserve (flag_preserve (flag_preserve hflag2 hx20_3 hx21_3) hx20_4 hx21_4) hx20_5 hx21_5
      have hok3 := step_post_chain_into_pb_31734_placed (M := M) (A := A) (ext := ext) s5 c2.intoPb
        (((s.sp + 0x28#64) ↦₆₄ mkCap) ∗ ((s.sp + 0x8#64) ↦₆₄ mkPtr) ∗ vecU8Heap A.repAlloc mkCap mkPtr msgKey ∗
          memRegion (s.sp + 0x1260#64) 88 ∗ memRegion (s.sp + 0x590#64) 88 ∗ memRegion ret 72 ∗
          chunkedStatesAt A.repAlloc (s.sp + 0x190#64) st1 ∗ chunkedStatesLocal1JumpTablePlacedAt ∗
          A.pool lim (M.stepEvents evs₂ (M.stepEvents evs₁ st)) s5 ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
        hpc5 hrun5 hx28_50 hsp5_align
      rw [hsp5] at hok3; apply of_sepWP_lscro_b1 (mid := spqrSendPlacedEntry + 4000#64) hinv5
      refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) (SepWP.mono hok3 ?_)
      rintro sf Q hpcf hrunf ⟨hvmf, _, htrf, hspf, hx19f, hx20f, hx21f, hx22f, hx23f, hx24f, hx26f, _, hx28f, hvregsf, hQ⟩ hinvf
      have hEnv_ok : SendKeyIntoPbEnv hkdf c1 msgEpoch (evs₁ ++ evs₂) := by
        unfold SendKeyIntoPbEnv; simp only [hep0, ↓reduceIte, hsk]; exact SeqEnv.append h1_env h_ipb2
      refine SepWPp.done hpcf hrunf
        ⟨evs₁ ++ evs₂, hEnv_ok, hrunf, htrf.trans (htr5.trans htr4_0), hspf, hinvf,
         hx19f.trans (hx19_5.trans (hx19_4.trans (hx19_3.trans hx19_20))), hx22f.trans (hx22_5.trans hx22_4),
         hx23f.trans (hx23_5.trans (hx23_4.trans (hx23_3.trans hx23_20))),
         hx24f.trans ((readReg32_of_readReg64_eq hx24_5).trans (hx24_4.trans hx24_3)),
         hx26f.trans (hx26_5.trans (hx26_4.trans (hx26_3.trans hx26_20))),
         hx28f.trans (hx28_5.trans (hx28_4.trans (hx28_3.trans hx28_20))),
         flag_preserve hflag5 hx20f hx21f,
         hvregsf.trans (hvregs5.trans (hvregs4.trans (hvregs3.trans hvregs2_0))), ?_⟩
      rw [M.stepEvents_append]
      rw [← A.pool_of_vmPreserved hvmf] at hQ
      let Mk := ((s.sp + 0x28#64) ↦₆₄ mkCap) ∗ ((s.sp + 0x8#64) ↦₆₄ mkPtr) ∗ vecU8Heap A.repAlloc mkCap mkPtr msgKey
      let Tail := memRegion (s.sp + 0x590#64) 88 ∗ memRegion (s.sp + 0x1260#64) 88 ∗
        memRegion (s.sp + 0x1060#64) 80 ∗ memRegion ret 72 ∗ chunkedStatesAt A.repAlloc (s.sp + 0x190#64) st1 ∗
        chunkedStatesLocal1JumpTablePlacedAt ∗ A.pool lim (M.stepEvents evs₂ (M.stepEvents evs₁ st)) sf ∗
        stackAt s.sp spqrSendCalleeStack ∗ Frame
      refine Entails.trans hQ (Entails.trans (Entails.of_eq (show
        optChainPBRegSlotAt A.repAlloc (s.sp + 0xd90#64) (sf.readReg64 .x25) (some c2.intoPb) ∗
          memRegion (s.sp + 0x1060#64) 80 ∗
          (((s.sp + 0x28#64) ↦₆₄ mkCap) ∗ ((s.sp + 0x8#64) ↦₆₄ mkPtr) ∗ vecU8Heap A.repAlloc mkCap mkPtr msgKey ∗
            memRegion (s.sp + 0x1260#64) 88 ∗ memRegion (s.sp + 0x590#64) 88 ∗ memRegion ret 72 ∗
            chunkedStatesAt A.repAlloc (s.sp + 0x190#64) st1 ∗ chunkedStatesLocal1JumpTablePlacedAt ∗
            A.pool lim (M.stepEvents evs₂ (M.stepEvents evs₁ st)) sf ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame) =
        Mk ∗ (optChainPBRegSlotAt A.repAlloc (s.sp + 0xd90#64) (sf.readReg64 .x25) (some c2.intoPb) ∗ Tail)
        by dsimp only [Mk, Tail]; sep_ac_rfl)) ?_)
      have hex_mk : Mk ⊢ ∃∗ mkCap : BitVec 64, ∃∗ mkPtr : BitVec 64,
          ((s.sp + 0x28#64) ↦₆₄ mkCap) ∗ ((s.sp + 0x8#64) ↦₆₄ mkPtr) ∗ vecU8Heap A.repAlloc mkCap mkPtr msgKey :=
        Entails.sepExists_right mkCap (Entails.sepExists_right mkPtr (Entails.refl _))
      exact Entails.trans (sepConj_mono_left hex_mk) (Entails.of_eq (by dsimp only [Tail]; sep_ac_rfl))

theorem addsPState64_noneCap_z : (addsPState64 noneCap 1#64).z = true := by
  unfold addsPState64 AddWithCarry64 noneCap; decide

theorem addsPState64_z_false_of_ne_noneCap {x21 : BitVec 64} (hne : x21 ≠ noneCap) :
    (addsPState64 x21 1#64).z = false := by
  unfold addsPState64 AddWithCarry64 noneCap at *
  simp only [Bool.false_eq_true, ↓reduceIte, beq_eq_false_iff_ne]; intro h; apply hne; bv_omega

theorem setPC_preserves {s1 s : State} {pc : BitVec 64} (h : s1 = s.setPC pc) :
    s1.sp = s.sp ∧ s1.trace = s.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s ∧ (∀ r, s1.readReg64 r = s.readReg64 r) := by
  subst h; exact ⟨rfl, rfl, rfl, fun _ => rfl⟩

theorem step_chain_5b8_to_7fc_placed {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {F : ShaCompress} (hkdf : HkdfFn) {ext : String → Option (State → State)}
    (hpanic_sub : ext "_RNvNtNtCskxtBwYRO61I_4core9panicking11panic_const24panic_const_sub_overflow" = some Rust.panicked)
    (hdealloc : DeallocOkPlaced M A lim ext)
    (hdrop_slice : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 446) (withLsCodeLoaded lsmpl (dropChainEpochSliceSpec M A lim)))
    (hdrop_states : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 443) (withLsCodeLoaded lsmpl (dropChunkedStatesLocal1PlacedSpec M A lim F)))
    (hadd_epoch : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 368) (withLsCodeRoLoaded lsmpl (chainAddEpochSpecX hkdf M A lim)))
    (hsend_key : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 367) (withLsCodeRoLoaded lsmpl (chainSendKeySpecX hkdf M A lim)))
    (hinto_pb : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 365) (withLsCodeRoLoaded lsmpl (chainIntoPbSpecX M A lim)))
    (s0 s : State) (st : M.σ) (ret x21 x27 x23 : BitVec 64)
    (c0 : Chain) (hc0_len : c0.links.length ≤ 2 ^ 54)
    (key : Option EpochSecret) (msgEpoch : Epoch) (st1 : States spqrPolyApi (spqrAuthApi F))
    (Frame Fr : SepProp) (φ_out : State → Prop)
    (hFit : FitsEnv M lim st (SendStepChainEnv hkdf (some c0) key msgEpoch))
    (hinv : LibsignalCodeRoLoaded lsmpl s.mem) (hpc : s.pc = spqrSendPlacedEntry + 3420#64)
    (hrun : s.status = .Running) (htr : s.trace = s0.trace) (hpstate : s.pstate = addsPState64 x21 1#64)
    (hx19 : s.readReg64 .x19 = ret) (hx21 : s.readReg64 .x21 = x21)
    (hx22 : s.readReg64 .x22 = msgEpoch) (hx23 : s.readReg64 .x23 = x23)
    (hx26 : s.readReg64 .x26 = s.sp + 0x1260#64) (hx27 : s.readReg64 .x27 = x27)
    (hx28 : s.readReg64 .x28 = s.sp + 0x1060#64)
    (hflag : s.readReg64 .x21 = noneCap ∨ s.readReg32 .x20 = 0#32)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hφ : ∀ sf : State, (sendStepChain hkdf (some c0) key msgEpoch).isPanic = true ∧ sf.trace = s0.trace → φ_out sf)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0 := by simp only [wp_norm, arm64_norm, *]) :
    SepWPp (spqrSendPlacedProg ext) (sendChainTargetPCPlaced (sendStepChain hkdf (some c0) key msgEpoch)) s
      (optEpochSecretRegSlotAt A.repAlloc s.sp x21 x27 key ∗ chainRepr A.repAlloc (s.sp + 0x590#64) c0 ∗
        memRegion (s.sp + 0x1260#64) 88 ∗ memRegion (s.sp + 0x1060#64) 80 ∗ memRegion (s.sp + 0xd90#64) 72 ∗
        memRegion (s.sp + 0x28#64) 8 ∗ memRegion (s.sp + 0x8#64) 8 ∗ memRegion ret 72 ∗
        chunkedStatesAt A.repAlloc (s.sp + 0x190#64) st1 ∗ chunkedStatesLocal1JumpTablePlacedAt ∗
        A.pool lim st s ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
      (sendChainPostPlaced A lim st (SendStepChainEnv hkdf (some c0) key msgEpoch) s0 s.sp ret x23 st1
        (memRegion (s.sp + 0x1bc0#64) 16 ∗ Frame) (sendStepChain hkdf (some c0) key msgEpoch))
      (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ (⌜φ_out sf⌝ ∗ anyHeap) ∗ Fr)) := by
  cases key with
  | none =>
    have heq_step : sendStepChain hkdf (some c0) none msgEpoch = sendKeyIntoPbChain hkdf c0 msgEpoch := rfl
    rw [heq_step]; dsimp only [optEpochSecretRegSlotAt]; rw [sepConj_assoc]
    apply pure_elim_focus_b1 (x21 = noneCap); intro hx21_none
    have hz : s.pstate.z = true := by rw [hpstate, hx21_none]; exact addsPState64_noneCap_z
    apply of_sepWP_lscro_b1 (mid := spqrSendPlacedEntry + 3456#64) hinv
    refine SepWP.mono (step_branch_key_none_315b8_placed s _ hpc hrun hz) ?_
    rintro s1 P1 hpc1 hrun1 ⟨hvm1, hs1, rfl⟩ hinv1
    rcases setPC_preserves hs1 with ⟨hsp1, htr1, hvregs1, hreg1⟩; rw [← A.pool_of_vmPreserved hvm1]
    have hstep := step_chain_5dc_to_7fc_placed hkdf hpanic_sub hdealloc hdrop_slice hdrop_states hsend_key hinto_pb
      s0 s1 st ret x23 c0 msgEpoch st1 (memRegion (s.sp + 0x1bc0#64) 16 ∗ Frame) Fr φ_out
      hFit hinv1 hpc1 hrun1 (htr1.trans htr)
      ((hreg1 .x19).trans hx19) ((hreg1 .x22).trans hx22) ((hreg1 .x23).trans hx23)
      (by rw [hsp1]; exact (hreg1 .x26).trans hx26) (by rw [hsp1]; exact (hreg1 .x28).trans hx28)
      (flag_preserve hflag (hreg1 .x20) (hreg1 .x21)) (by rw [hsp1]; exact hsp_align) hφ (hvregs1.trans hvregs)
    rw [hsp1] at hstep; exact SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl)) hstep
  | some es =>
    have hexp_ne : optEpochSecretRegSlotAt A.repAlloc s.sp x21 x27 (some es) ⊢
        ⌜x21 ≠ noneCap⌝ ∗ optEpochSecretRegSlotAt A.repAlloc s.sp x21 x27 (some es) := by
      dsimp only [optEpochSecretRegSlotAt]; apply Entails.pure_left; intro hne
      exact Entails.pure_right hne (Entails.pure_right hne (Entails.refl _))
    refine SepWPp.weaken_pre (sepConj_mono_left hexp_ne) ?_; rw [sepConj_assoc]
    apply pure_elim_focus_b1 (x21 ≠ noneCap); intro hx21_ne
    have hz : s.pstate.z = false := by rw [hpstate]; exact addsPState64_z_false_of_ne_noneCap hx21_ne
    apply of_sepWP_lscro_b1 (mid := spqrSendPlacedEntry + 3424#64) hinv
    refine SepWP.mono (step_branch_key_some_315b8_placed s _ hpc hrun hz) ?_
    rintro s1 P1 hpc1 hrun1 ⟨hvm1, hs1, rfl⟩ hinv1
    rcases setPC_preserves hs1 with ⟨hsp1, htr1, hvregs1, hreg1⟩; rw [← A.pool_of_vmPreserved hvm1]
    have hx19_1 : s1.readReg64 .x19 = ret := (hreg1 .x19).trans hx19
    have hx21_1 : s1.readReg64 .x21 = x21 := (hreg1 .x21).trans hx21
    have hx22_1 : s1.readReg64 .x22 = msgEpoch := (hreg1 .x22).trans hx22
    have hx23_1 : s1.readReg64 .x23 = x23 := (hreg1 .x23).trans hx23
    have hx26_1 : s1.readReg64 .x26 = s.sp + 0x1260#64 := (hreg1 .x26).trans hx26
    have hx27_1 : s1.readReg64 .x27 = x27 := (hreg1 .x27).trans hx27
    have hx28_1 : s1.readReg64 .x28 = s.sp + 0x1060#64 := (hreg1 .x28).trans hx28
    rw [memRegion_1260_88_eq_32_56 s.sp]
    have hpre_ae := step_pre_add_epoch_315bc_placed (M := M) (A := A) (ext := ext) s1 es
      (chainRepr A.repAlloc (s.sp + 0x590#64) c0 ∗ memRegion (s.sp + 0x1280#64) 56 ∗
        memRegion (s.sp + 0x1060#64) 80 ∗ memRegion (s.sp + 0xd90#64) 72 ∗ memRegion (s.sp + 0x28#64) 8 ∗
        memRegion (s.sp + 0x8#64) 8 ∗ memRegion ret 72 ∗ chunkedStatesAt A.repAlloc (s.sp + 0x190#64) st1 ∗
        chunkedStatesLocal1JumpTablePlacedAt ∗ A.pool lim st s1 ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
      hpc1 hrun1 (by rw [hsp1]; exact hsp_align)
    rw [hsp1, hx21_1, hx27_1] at hpre_ae; apply of_sepWP_lscro_b1 (mid := lsmpl.base 368) hinv1
    refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) (SepWP.mono hpre_ae ?_)
    rintro s2 P2 hpc2 hrun2 ⟨hvm2, _, htr2, hsp2, hx0_2, hx1_2, hx30_2, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, _, _, hx26_2, _, hx28_2, hvregs2, hP2⟩ hinv2
    have hP2' : P2 ⊢ chainRepr A.repAlloc (s.sp + 0x590#64) c0 ∗
        epochSecretAt A.repAlloc (s.sp + 0x1260#64) ⟨x21, x27⟩ es ∗
        memRegion (s.sp + 0x1bc0#64) 16 ∗ memRegion (s.sp + 0x1280#64) 56 ∗ memRegion (s.sp + 0x1060#64) 80 ∗
        memRegion (s.sp + 0xd90#64) 72 ∗ memRegion (s.sp + 0x28#64) 8 ∗ memRegion (s.sp + 0x8#64) 8 ∗ memRegion ret 72 ∗
        chunkedStatesAt A.repAlloc (s.sp + 0x190#64) st1 ∗ chunkedStatesLocal1JumpTablePlacedAt ∗
        A.pool lim st s2 ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame := by
      rw [A.pool_of_vmPreserved hvm2]; exact Entails.trans hP2 (Entails.of_eq (by sep_ac_rfl))
    refine SepWPp.weaken_pre hP2' ?_; dsimp only [chainRepr]; rw [sepExists_sepConj_left]
    apply SepWPp.exists_elim; intro G0
    refine SepWPp.weaken_pre (sepConj_mono_left (chainAt_entails_links_grow_ok A.repAlloc (s.sp + 0x590#64) G0 c0 hc0_len)) ?_
    rw [sepConj_assoc]
    apply pure_elim_focus_b1 (c0.links.length < G0.linksCap.toNat ∨ max (2 * G0.linksCap.toNat) 4 * chainEpochSize < 2 ^ 63)
    intro hgrow
    have htr2_0 : s2.trace = s0.trace := htr2.trans (htr1.trans htr)
    have hlr_ae : LsRetAddr624 (s2.readReg64 .lr) :=
      hx30_2.symm ▸ lsRetAddr624_base_add 427 3456#64 (by decide) (by decide)
    let x_ae : ChainAddEpochGhost := ⟨s.sp + 0x590#64, s.sp + 0x1260#64, G0, ⟨x21, x27⟩, c0, es⟩
    have hpan_ae : ∀ sm : State, (Chain.addEpoch hkdf c0 es).isOk = false ∧ sm.trace = s2.trace → φ_out sm := by
      intro sm ⟨hpan_ae, htr_sm⟩; refine hφ sm ⟨?_, htr_sm.trans htr2_0⟩
      unfold sendStepChain; dsimp only [Bind.bind, Except.bind]
      cases h : Chain.addEpoch hkdf c0 es with
      | ok _ => rw [h] at hpan_ae; contradiction
      | error _ => rfl
    cases hae : Chain.addEpoch hkdf c0 es with
    | error p =>
      have hFit_ae : FitsEnv M lim st (ChainAddEpochEnv hkdf x_ae) := by
        intro evs hevs; dsimp only [ChainAddEpochEnv, x_ae] at hevs; rw [hae] at hevs; subst hevs; trivial
      exact panic_lscro_calleeStack_anyPanic (s.sp) chainAddEpochStackX (by decide) (x := (x_ae, st))
        (T_pre := chainAt A.repAlloc (s.sp + 0x590#64) G0 c0 ∗
          epochSecretAt A.repAlloc (s.sp + 0x1260#64) ⟨x21, x27⟩ es ∗ A.pool lim st s2)
        (F := memRegion (s.sp + 0x1bc0#64) 16 ∗ memRegion (s.sp + 0x1280#64) 56 ∗ memRegion (s.sp + 0x1060#64) 80 ∗
          memRegion (s.sp + 0xd90#64) 72 ∗ memRegion (s.sp + 0x28#64) 8 ∗ memRegion (s.sp + 0x8#64) 8 ∗ memRegion ret 72 ∗
          chunkedStatesAt A.repAlloc (s.sp + 0x190#64) st1 ∗ chunkedStatesLocal1JumpTablePlacedAt ∗ Frame)
        (φ_pre := s2.readReg64 .x0 = x_ae.selfPtr ∧ s2.readReg64 .x1 = x_ae.esPtr ∧
          (x_ae.self.links.length < x_ae.G.linksCap.toNat ∨ max (2 * x_ae.G.linksCap.toNat) 4 * chainEpochSize < 2 ^ 63) ∧
          FitsEnv M lim st (ChainAddEpochEnv hkdf x_ae) ∧
          LsRetAddr624 (s2.readReg64 .lr))
        hadd_epoch hinv2 hpc2 hrun2 hsp2 hsp_align (by dsimp only [chainAddEpochSpecX, x_ae]; sep_ac_rfl)
        ⟨hx0_2, hx1_2, hgrow, hFit_ae, hlr_ae⟩ (by sep_ac_rfl) (fun _ _ => rfl) (fun _ => rfl) hpan_ae
        (fun _ => by dsimp only [chainAddEpochSpecX, x_ae]; rw [hae])
    | ok c1 =>
      have hFit' : FitsEnv M lim st (SeqEnv (AddEpochFirstEnv hkdf c0 es) (SendKeyIntoPbEnv hkdf c1 msgEpoch)) :=
        FitsEnv.mono (fun evs he => by unfold SendStepChainEnv; simp only [hae]; exact he) hFit
      have hFit_ae : FitsEnv M lim st (ChainAddEpochEnv hkdf x_ae) :=
        FitsEnv.mono (fun evs he => ⟨x_ae, rfl, rfl, hgrow, he⟩) hFit'.seq_left
      refine call_lscro_calleeStack_anyPanic (s.sp) chainAddEpochStackX (by decide) (x := (x_ae, st))
        (T_pre := chainAt A.repAlloc (s.sp + 0x590#64) G0 c0 ∗
          epochSecretAt A.repAlloc (s.sp + 0x1260#64) ⟨x21, x27⟩ es ∗ A.pool lim st s2)
        (T_post := fun sf => chainRepr A.repAlloc (s.sp + 0x590#64) c1 ∗ memRegion (s.sp + 0x1260#64) 32 ∗
          A.pool lim (M.stepEvents (chainAddEpochEvents x_ae) st) sf)
        (F := memRegion (s.sp + 0x1bc0#64) 16 ∗ memRegion (s.sp + 0x1280#64) 56 ∗ memRegion (s.sp + 0x1060#64) 80 ∗
          memRegion (s.sp + 0xd90#64) 72 ∗ memRegion (s.sp + 0x28#64) 8 ∗ memRegion (s.sp + 0x8#64) 8 ∗ memRegion ret 72 ∗
          chunkedStatesAt A.repAlloc (s.sp + 0x190#64) st1 ∗ chunkedStatesLocal1JumpTablePlacedAt ∗ Frame)
        (φ_pre := s2.readReg64 .x0 = x_ae.selfPtr ∧ s2.readReg64 .x1 = x_ae.esPtr ∧
          (x_ae.self.links.length < x_ae.G.linksCap.toNat ∨ max (2 * x_ae.G.linksCap.toNat) 4 * chainEpochSize < 2 ^ 63) ∧
          FitsEnv M lim st (ChainAddEpochEnv hkdf x_ae) ∧
          LsRetAddr624 (s2.readReg64 .lr))
        (φ_post := fun sf => sf.trace = s2.trace ∧ AllocCallPreserved s2 sf)
        hadd_epoch hinv2 hpc2 hrun2 hsp2 hsp_align hx30_2 (by dsimp only [chainAddEpochSpecX, x_ae]; sep_ac_rfl)
        ⟨hx0_2, hx1_2, hgrow, hFit_ae, hlr_ae⟩ (by sep_ac_rfl) (fun _ _ => rfl) (fun _ => rfl) hpan_ae
        (fun _ => by dsimp only [chainAddEpochSpecX, x_ae]; rw [hae]; sep_ac_rfl) ?_
      intro s3 hpc3 hrun3 hsp3 ⟨htr3, _⟩ hinv3 hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 _ _ hx26_3 _ hx28_3 hvregs3
      have heq_step : sendStepChain hkdf (some c0) (some es) msgEpoch = sendKeyIntoPbChain hkdf c1 msgEpoch := by
        unfold sendStepChain sendKeyIntoPbChain; simp [hae]; rfl
      have h1_ae : AddEpochFirstEnv hkdf c0 es (chainAddEpochEvents x_ae) :=
        ⟨x_ae, rfl, rfl, hgrow, by dsimp only [ChainAddEpochEnv, x_ae]; rw [hae]⟩
      have hFit_sk : FitsEnv M lim (M.stepEvents (chainAddEpochEvents x_ae) st)
          (SendKeyIntoPbEnv hkdf c1 msgEpoch) := hFit'.seq_right h1_ae
      rw [heq_step]
      have hsp3_align : (s3.sp &&& 15#64 == 0#64) = true := by rw [hsp3]; exact hsp_align
      have hx19_30 : s3.readReg64 .x19 = ret := hx19_3.trans (hx19_2.trans hx19_1)
      have hx22_30 : s3.readReg64 .x22 = msgEpoch := hx22_3.trans (hx22_2.trans hx22_1)
      have hx23_30 : s3.readReg64 .x23 = x23 := hx23_3.trans (hx23_2.trans hx23_1)
      have hx26_30 : s3.readReg64 .x26 = s3.sp + 0x1260#64 := by rw [hsp3]; exact hx26_3.trans (hx26_2.trans hx26_1)
      have hx28_30 : s3.readReg64 .x28 = s3.sp + 0x1060#64 := by rw [hsp3]; exact hx28_3.trans (hx28_2.trans hx28_1)
      have hflag3 := flag_preserve (flag_preserve (flag_preserve hflag (hreg1 .x20) (hreg1 .x21)) hx20_2 (hx21_2.trans hx21_1.symm)) hx20_3 hx21_3
      have hstep := step_chain_5dc_to_7fc_placed hkdf hpanic_sub hdealloc hdrop_slice hdrop_states hsend_key hinto_pb
        s0 s3 (M.stepEvents (chainAddEpochEvents x_ae) st) ret x23 c1 msgEpoch st1
        (memRegion (s.sp + 0x1bc0#64) 16 ∗ Frame) Fr φ_out hFit_sk hinv3 hpc3 hrun3 (htr3.trans htr2_0)
        hx19_30 hx22_30 hx23_30 hx26_30 hx28_30 hflag3 hsp3_align (by rwa [heq_step] at hφ)
        (hvregs3.trans (hvregs2.trans (hvregs1.trans hvregs)))
      rw [hsp3, memRegion_1260_88_eq_32_56 s.sp] at hstep
      refine sepWPp_mono_post (fun sf Pf hQ => ?_) (SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl)) hstep)
      refine sendChainPostPlaced_mono (fun evs he => ?_) (sendChainPostPlaced_step h1_ae hQ)
      unfold SendStepChainEnv; simp only [hae]; exact he

end LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesBridge1PlacedBudgetAux
