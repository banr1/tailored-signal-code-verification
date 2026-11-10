/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Common.SharedHelpers
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemP2TopArmsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemP2ArmsPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2V1PlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2V1PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1Msg
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import ProofLib.SepLogic.WPp
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Comb
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2ArmsPlacedBudget
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2BlocksB5PlacedBudget
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsBudget
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlaced
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudget
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2ErrArmsAPlacedBudget
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2ErrArmsBPlacedBudget
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2ErrArmsCPlacedBudget
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Mid3PlacedBudget
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub1
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub2
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub5AuxPlacedBudget
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub5Defs
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub5DefsPlaced
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub5DefsPlacedBudget
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub5V1PlacedBudget
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2TransPlaced
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2ArmsAPlacedBudget
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2ErrBPlacedBudget
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2ErrCPlacedBudget
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2Mid3PlacedBudget
import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.InitializeAliceStage1Common
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP2bAux
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Fetch

/-!
# Budget-Threaded Substage P2.5 (`+0x1168 → initialize_bob_session`) on Bad-KEM

Steps Substage P2.5 from `+0x1168` (`is_same_account`) through `+0x11d0` to the
`initialize_bob_session` call under `StageP2MemInv` and `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

open scoped CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchet
open CryptoGames.LibsignalSession (IdentityKey)
open CryptoVerification (LibsignalFrozen LibsignalPlacement libsignalSessionLib lsLogFilterAddr lsmpl withLsCodeLoaded)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits (StageP2MemInv p2_call_nopanic_lscl_steps_frame_placed p2_sepWPp_weaken_eq p2_stackAt_split_of_le stageP1EntryPlaced stageP1ProgPlaced)
open CryptoVerification.E2E.Pqxdh.Initiator (AcceptKeysInput WellSizedAcceptKeysInput bytesToBv8 pqxdhEntryStack)
open CryptoVerification.E2E.Pqxdh.ResponderClosure (coro658_298_eq decryptPrekeySavedRegsAt exists_words4_of_len32 identityKey_ne_of_bytes_ne memRegion65_eq_words8_byte opkPresentTag opkSlot65_eq_optField opkUnusedFieldAt sp3e0_344_split_65_279 stageP2bStack words4_entails_cells4 words8_byte_entails_memRegion65 words8_entails_cells8 words8_entails_memRegion64)
open CryptoVerification.E2E.Pqxdh.ResponderCore (bytesToBv8_length withBobMemInv)
open CryptoVerification.E2E.Pqxdh.WireEntries (DistinctSid)
open CryptoVerification.LibsignalPublicApi.StoreKit (speWordsAt)
open CryptoVerification.LibsignalTripleRatchet (withLsFrozen)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost protocolAddressAt uuidTryParse)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2BlocksB5PlacedBudget (p2_seg5c3_ext_placed_wp p2_seg5d_ext_placed_wp)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsBudget (isSameAccountDistinctAtSpec)

namespace LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemP2TopSub5APlacedBudget

open Arm64 ProofLib SepProp ProofLib.ProgramReflection ProofLib.Variant
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget (dropSessionStructureLocal2Spec)
open CryptoVerification.SignalSession.Cli.RunProofs.Poll (
  signalMessageRestVerAt signalMessageAt_eq_ver_sep memRegion_4_eq_exists_pointsTo32
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Mid3PlacedBudget (
  P2Sub1To4Env P2Sub1To4OkEnv P2Sub1To3Arm1Env P2Sub1To3Arm2Env P2Sub1To4Arm3Env
  stageP2_sub1_to_4_kits_ext_placed_ofEnv
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2ArmsPlacedBudget (
  p2Sub5FramePlaced
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub5DefsPlacedBudget (
  p2_entails_frame_v1 p2_call_nopanic_rocl_sub5 p2_bind_sepWP_steps_cro_sub5_qpan
  p2_bind_sepWP_steps_cro_sub5_state
  isSameAccountDistinctSpec_to_at_placed p2_stageP2bStack_le_bobV1 p2_isSameAccount_le_bobV1
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2V1PlacedBudget (
  P2V1Arm4Env P2V1Arm5EnvOfAcceptErr
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2ArmsAPlacedBudget (
  p2OverSub5FramePlaced
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2ErrBPlacedBudget (
  p2_over_arm4_err_hooks_placed_ok
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2ErrCPlacedBudget (
  p2_over_arm5_err_hooks_placed_ok
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2Mid2PlacedBudget (
  P2OverSub1To3Arm1Env P2OverSub1To3Arm2Env
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2Mid3PlacedBudget (
  P2OverSub1To4Env P2OverSub1To4OkEnv P2OverSub1To4Arm3Env
  stageP2_over_sub1_to_4_kits_ext_placed_ofEnv
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2V1PlacedBudget (
  P2OverV1Arm4Env P2OverV1Arm5EnvOfAcceptErr
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemBobAuxPlacedBudget (
  AcceptBadKemEnv initializeBobSessionBadKemErrOwnedInnerPlacedSpec
  initializeBobSessionBadKemErrOwnedPlacedSpec initializeBobSessionBadKemErrOwnedFrozenPlacedSpec
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemP2KitsPlacedBudget (
  p2BadKemSub1To4Frame p2BadKemErrFrameAtPlaced stageP2BadKemPreAtPlaced
  stageP2OverBadKemPreAtPlaced p2_initBobBadKemErrOwnedAt_unpack
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemP2ArmsPlacedBudget (
  p2_badKem_entry_to_sub1To4_placed p2_over_badKem_entry_to_sub1To4_placed
  p2_badKem_sub4_to_sub5_placed p2_over_badKem_sub4_to_sub5_placed
  p2_badKem_arm5_err_payload_pull_placed
  p2_badKem_arm1_entails_placed p2_badKem_arm2_entails_placed p2_badKem_arm3_entails_placed
)

set_option allowUnsafeReducibility true in
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  protocolAddressAt decryptPrekeySavedRegsAt
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem eq_of_sep_emp {P Q : SepProp} (h : P = Q ∗ emp) : P = Q :=
  h.trans (sepConj_emp Q)

/-! ## `StageP2MemInv`-Parameterized Substage P2.5 Tail -/

theorem p2_badKem_entry_le_stageP2bStack : 768 + pqxdhEntryStack ≤ stageP2bStack := by decide

theorem of_cro_badKem_errOwned_placed [LibsignalPlacement] {prog : Program} {entry : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    (h : subroutine_ok prog entry (LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemBobAuxPlacedBudget.initializeBobSessionBadKemErrOwnedPlacedSpec A lim AcceptErrEnv)) :
    subroutine_ok prog entry
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (withBobMemInv (CryptoVerification.LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl)
          (LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemBobAuxPlacedBudget.initializeBobSessionBadKemErrOwnedInnerPlacedSpec A lim AcceptErrEnv))) := by
  refine subroutine_ok_map_panic h ?_
    (fun _ _ _ _ _ _ he => by
      dsimp only [LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemBobAuxPlacedBudget.initializeBobSessionBadKemErrOwnedPlacedSpec,
        LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemBobAuxPlacedBudget.initializeBobSessionBadKemErrOwnedInnerPlacedSpec, CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded, CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded] at he
      exact not_satisfies_false_sepConj he)
    (fun _ _ _ _ _ _ _ ho => by
      dsimp only [LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemBobAuxPlacedBudget.initializeBobSessionBadKemErrOwnedPlacedSpec,
        LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemBobAuxPlacedBudget.initializeBobSessionBadKemErrOwnedInnerPlacedSpec, CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded, CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded] at ho
      exact (not_satisfies_false_sepConj ho).elim)
  intro g R s0 hpre
  refine ⟨g, R, ?_, fun sf hpost => hpost, fun sf hpan => hpan⟩
  dsimp only [LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemBobAuxPlacedBudget.initializeBobSessionBadKemErrOwnedPlacedSpec,
    LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemBobAuxPlacedBudget.initializeBobSessionBadKemErrOwnedInnerPlacedSpec, CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded,
    CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded, withBobMemInv] at hpre ⊢
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  exact hpre.2

theorem of_full_badKem_errOwned_placed [LibsignalPlacement] {prog : Program} {entry : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    (h : subroutine_ok prog entry (LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemBobAuxPlacedBudget.initializeBobSessionBadKemErrOwnedFrozenPlacedSpec A lim AcceptErrEnv)) :
    subroutine_ok prog entry
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (withBobMemInv (LibsignalFrozen lsmpl)
          (LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemBobAuxPlacedBudget.initializeBobSessionBadKemErrOwnedInnerPlacedSpec A lim AcceptErrEnv))) := by
  refine subroutine_ok_map_panic h ?_
    (fun _ _ _ _ _ _ he => by
      dsimp only [LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemBobAuxPlacedBudget.initializeBobSessionBadKemErrOwnedFrozenPlacedSpec,
        LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemBobAuxPlacedBudget.initializeBobSessionBadKemErrOwnedInnerPlacedSpec, withLsFrozen] at he
      exact not_satisfies_false_sepConj he)
    (fun _ _ _ _ _ _ _ ho => by
      dsimp only [LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemBobAuxPlacedBudget.initializeBobSessionBadKemErrOwnedFrozenPlacedSpec,
        LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemBobAuxPlacedBudget.initializeBobSessionBadKemErrOwnedInnerPlacedSpec, withLsFrozen] at ho
      exact (not_satisfies_false_sepConj ho).elim)
  intro g R s0 hpre
  refine ⟨g, R, ?_, fun sf hpost => hpost, fun sf hpan => hpan⟩
  dsimp only [LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemBobAuxPlacedBudget.initializeBobSessionBadKemErrOwnedFrozenPlacedSpec,
    LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemBobAuxPlacedBudget.initializeBobSessionBadKemErrOwnedInnerPlacedSpec, CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded,
    withBobMemInv, withLsFrozen] at hpre ⊢
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  exact hpre.2

private theorem p2_call_memInv_nopanic_steps_frame_sub5 [LibsignalPlacement] {Φ : Memory → Prop}
    (hInv : StageP2MemInv Φ) {α : Type} {prog : Program}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State} {φ : Prop}
    {P T F : SepProp} {Q Qp : State → SepProp → Prop}
    (hΦ : Φ s.mem)
    (hcall : subroutine_ok prog entry (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (withBobMemInv Φ spec)))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hnext : ∀ sf : State, Steps prog s sf → sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      Φ sf.mem → SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hpan_false : ∀ sf, spec.onPanic x s sf = ⌜False⌝ := by intro _; rfl)
    (hexit_false : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intro _ _; rfl)
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intro _; rfl) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  have hm0 : s.mem ⊨ spec.pre x s ∗ (F ∗ R) :=
    Arm64.Satisfies.mono (sepConj_mono_left (by rw [hspec]; exact Entails.pure_right hφ (Entails.refl T))) hm
  have hm' : s.mem ⊨ (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (withBobMemInv Φ spec)).pre x s ∗ (F ∗ R) := by
    dsimp only [CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded, withBobMemInv]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hInv.toCodeRo hΦ, ?_⟩
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨hΦ, hm0⟩
  obtain ⟨sm, hsteps, hout, _⟩ := hcall.no_fault_before_outcome x (F ∗ R) s hpc hrun hm' hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨_, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, hpost⟩
  · dsimp only [CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded, withBobMemInv] at hpost
    rw [← sepConj_assoc] at hpost; rw [hlr] at hpcm
    have hsp_alm : sm.spAligned = true := by simpa [State.spAligned, hspm] using hsp
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hsteps hpcm hrunm hspm hsp_alm hcsm (hInv.of_keepsFrozen hΦ hsteps.keepsFrozen)
        R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · dsimp only [CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded, withBobMemInv] at hpost; rw [hpan_false] at hpost
    exact (not_satisfies_false_sepConj hpost).elim
  · dsimp only [CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded, withBobMemInv] at hpost; rw [hexit_false] at hpost
    exact (not_satisfies_false_sepConj hpost).elim
  · dsimp only [CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded, withBobMemInv] at hpost; rw [hoom_false] at hpost
    exact (not_satisfies_false_sepConj hpost).elim

theorem p2_bind_sepWP_steps_memInv_sub5_qpan [LibsignalPlacement]
    {Φ : Memory → Prop} (hInv : StageP2MemInv Φ) {prog : Program}
    {mid ret : BitVec 64} {s : State} {P P_seg F P_seg_post : SepProp}
    {Q_regs : State → Prop} {Q Qp : State → SepProp → Prop}
    (hΦ : Φ s.mem)
    (hseg : SepWP prog mid s P_seg (fun sm P_m => (P_m ⊢ P_seg_post) ∧ Q_regs sm))
    (hP : P = P_seg ∗ F)
    (hnext : ∀ sm : State, Steps prog s sm → sm.pc = mid → sm.status = .Running →
      Φ sm.mem → Q_regs sm → SepWPp prog ret sm (P_seg_post ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp :=
  LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub5DefsPlacedBudget.p2_bind_sepWP_steps_cro_sub5_qpan (hInv.toCodeRo hΦ) hseg hP
    fun sm hsteps hpcm hrunm _ hregs =>
      hnext sm hsteps hpcm hrunm (hInv.of_keepsFrozen hΦ hsteps.keepsFrozen) hregs

theorem p2_bind_sepWP_steps_memInv_sub5_state [LibsignalPlacement]
    {Φ : Memory → Prop} (hInv : StageP2MemInv Φ) {prog : Program}
    {mid ret : BitVec 64} {s : State} {P P_seg F : SepProp}
    {P_seg_post : State → SepProp} {Q_regs : State → Prop}
    {Q Qp : State → SepProp → Prop}
    (hΦ : Φ s.mem)
    (hseg : SepWP prog mid s P_seg (fun sm P_m => (P_m ⊢ P_seg_post sm) ∧ Q_regs sm))
    (hP : P = P_seg ∗ F)
    (hnext : ∀ sm : State, Steps prog s sm → sm.pc = mid → sm.status = .Running →
      Φ sm.mem → Q_regs sm → SepWPp prog ret sm (P_seg_post sm ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp :=
  p2_bind_sepWP_steps_cro_sub5_state (hInv.toCodeRo hΦ) hseg hP
    fun sm hsteps hpcm hrunm _ hregs =>
      hnext sm hsteps hpcm hrunm (hInv.of_keepsFrozen hΦ hsteps.keepsFrozen) hregs

set_option maxHeartbeats 1200000 in
theorem stageP2_sub5_tail_badKem_kits_memInv_at_placed [LibsignalPlacement]
    {Φ : Memory → Prop} (hInv : StageP2MemInv Φ) {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    (ext : String → Option (State → State)) {sameStk : Nat}
    (hSameAcct : subroutine_ok (stageP1ProgPlaced ext) (lsmpl.base 17)
      (withLsCodeLoaded lsmpl (isSameAccountDistinctAtSpec A.repAlloc uuidTryParse sameStk)))
    (hInitBobBadKemErrOwned : subroutine_ok (stageP1ProgPlaced ext) (lsmpl.base 75)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (withBobMemInv Φ (LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemBobAuxPlacedBudget.initializeBobSessionBadKemErrOwnedInnerPlacedSpec A lim AcceptErrEnv))))
    {st : M.σ} {Qp : State → SepProp → Prop}
    (inp : AcceptKeysInput) (ctBytes : List (BitVec 8)) (ikBPk spkBPk : SignalPqxdh.Bytes)
    (opkPkBytes opkSkBytes : List (BitVec 8)) (gMe gPeer : AddrGhost) (s0 s6 : State)
    (Q : State → SepProp → Prop)
    (sp coroPtr msgPtr remoteAddrPtr localAddrPtr kyberKpPubPtr kyberKpSecPtr ctBufPtr fp : BitVec 64)
    (ik0 ik1 ik2 ik3 ik4 ik5 ik6 ik7 u_950 u_958 u_960 u_968 : BitVec 64)
    (opk0 opk1 opk2 opk3 opk4 opk5 opk6 opk7 : BitVec 64) (opkId : BitVec 32)
    (opk_b64 b_4f1 : BitVec 8) (stk : Nat) (F_rest : SepProp)
    (htrusted : inp.trustedPeer = true) (hreplay : inp.replayOk = true)
    (hopk_match : inp.hdr.opkId?.isSome = inp.opkBSk?.isSome)
    (hwell : WellSizedAcceptKeysInput inp) (hikBPk_len : ikBPk.length = 32)
    (hspkBPk_len : spkBPk.length = 32) (hct_bd : ctBytes.length < 2 ^ 63)
    (hbadKem : pkVecTag? 8#8 1568 ctBytes = none)
    (hopkSk_eq : ∀ opkSk, inp.opkBSk? = some opkSk → opkSkBytes = bytesToBv8 opkSk)
    (hneq : ikBPk ≠ inp.hdr.ikAPk ∨ DistinctSid uuidTryParse gMe.name.bytes gPeer.name.bytes)
    (hikB0 : ∀ a : BitVec 64, ((a + 0#64) ↦ₛ bytesToBv8 ikBPk) =
      ((a + 0#64) ↦₆₄ ik0) ∗ ((a + 8#64) ↦₆₄ ik1) ∗ ((a + 16#64) ↦₆₄ ik2) ∗ ((a + 24#64) ↦₆₄ ik3))
    (hikB1 : ∀ a : BitVec 64, ((a + 0#64) ↦ₛ bytesToBv8 inp.ikBSk) =
      ((a + 0#64) ↦₆₄ ik4) ∗ ((a + 8#64) ↦₆₄ ik5) ∗ ((a + 16#64) ↦₆₄ ik6) ∗ ((a + 24#64) ↦₆₄ ik7))
    (hopk : ∀ a : BitVec 64,
      ((a + 0#64) ↦₈ opkPresentTag inp.opkBSk?) ∗ ((a + 1#64) ↦ₛ opkPkBytes) ∗ ((a + 33#64) ↦ₛ opkSkBytes) =
      ((a + 0#64) ↦₆₄ opk0) ∗ ((a + 8#64) ↦₆₄ opk1) ∗ ((a + 16#64) ↦₆₄ opk2) ∗
      ((a + 24#64) ↦₆₄ opk3) ∗ ((a + 32#64) ↦₆₄ opk4) ∗ ((a + 40#64) ↦₆₄ opk5) ∗
      ((a + 48#64) ↦₆₄ opk6) ∗ ((a + 56#64) ↦₆₄ opk7) ∗ ((a + 64#64) ↦₈ opk_b64))
    (hsame_le : sameStk ≤ stk) (herr_le : 768 + pqxdhEntryStack ≤ stk) (hstk_lt : stk ≤ sp.toNat)
    (hfits_err : FitsEnv M lim st (AcceptErrEnv inp)) (hCode6 : Φ s6.mem)
    (hpc6 : s6.pc = stageP1EntryPlaced + 0x1168#64) (hrun6 : s6.status = .Running)
    (hsp6 : s6.sp = sp) (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (hvregs6 : calleeSavedVRegs s6 = calleeSavedVRegs s0)
    (hx0_6 : s6.readReg64 .x0 = coroPtr + 0x798#64) (hx1_6 : s6.readReg64 .x1 = localAddrPtr)
    (hx2_6 : s6.readReg64 .x2 = msgPtr + 0xc8#64) (hx3_6 : s6.readReg64 .x3 = remoteAddrPtr)
    (hx8_6 : s6.readReg64 .x8 = opk_b64.zeroExtend 64) (hx9_6 : s6.readReg64 .x9 = msgPtr)
    (hx10_6 : s6.readReg64 .x10 = coroPtr + 0x798#64) (hx19_6 : s6.readReg64 .x19 = coroPtr)
    (hx21_6 : s6.readReg64 .x21 = msgPtr + 0x90#64) (hx22_6 : s6.readReg64 .x22 = sp + 0x370#64)
    (hx23_6 : s6.readReg64 .x23 = sp + 0x930#64) (hx24_6 : s6.readReg64 .x24 = coroPtr + 0x398#64)
    (hx28_6 : s6.readReg64 .x28 = sp + 0xa90#64) (hx29_6 : s6.readReg64 .x29 = fp)
    (hErrBob : ∀ (evs : List AllocEvent) (errTag w2 w3 w4 w5 w6 : BitVec 64) (sf : State),
      AcceptErrEnv inp evs → errTag ≠ -2#64 → errTag ≠ -3#64 →
      Steps (stageP1ProgPlaced ext) s6 sf → sf.pc = stageP1EntryPlaced + 0x125c#64 →
      sf.status = .Running → sf.sp = sp → sf.trace = s6.trace →
      sf.readReg64 .x19 = coroPtr → sf.readReg64 .x21 = msgPtr + 0x90#64 →
      sf.readReg64 .x22 = sp + 0x370#64 → sf.readReg64 .x23 = sp + 0x930#64 →
      sf.readReg64 .x24 = coroPtr + 0x398#64 → sf.readReg64 .x25 = s6.readReg64 .x25 →
      sf.readReg64 .x26 = s6.readReg64 .x26 → sf.readReg64 .x28 = sp + 0xa90#64 →
      sf.readReg64 .x29 = fp → calleeSavedVRegs sf = calleeSavedVRegs s0 →
      CryptoVerification.LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      SepWPp (stageP1ProgPlaced ext) (s0.readReg64 .x30) sf
        (((sp + 0x3e0#64) ↦₆₄ 0xffffffffffffffff#64) ∗
         speWordsAt (sp + 0x3e8#64) errTag w2 w3 w4 w5 w6 ∗
         pqxdhBadKemErrPayloadAt A.repAlloc errTag w2 w3 w4 ∗ memRegion (sp + 0x418#64) 288 ∗
         bobParamsBadKemFieldsAt (coroPtr + 0x658#64) kyberKpSecPtr (msgPtr + 0x90#64) ctBufPtr
           (coroPtr + 0x398#64) inp ctBytes ikBPk spkBPk 0#8 ∗
         ((coroPtr + 0x3d8#64) ↦₆₄ kyberKpPubPtr) ∗ ((coroPtr + 0x3e0#64) ↦₆₄ 0x620#64) ∗
         ((coroPtr + 0x3e8#64) ↦₆₄ kyberKpSecPtr) ∗ ((coroPtr + 0x3f0#64) ↦₆₄ 0xc60#64) ∗
         ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗ ((coroPtr + 0x470#64) ↦₆₄ remoteAddrPtr) ∗
         ((coroPtr + 0x478#64) ↦₆₄ localAddrPtr) ∗ ((coroPtr + 0x488#64) ↦₆₄ (msgPtr + 0x90#64)) ∗
         ((coroPtr + 0x4b0#64) ↦₈ opkPresentTag inp.opkBSk?) ∗
         ((coroPtr + 0x4b1#64) ↦ₛ opkPkBytes) ∗ ((coroPtr + 0x4d1#64) ↦ₛ opkSkBytes) ∗
         ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗ ((coroPtr + 0x698#64) ↦ₛ bytesToBv8 spkBPk) ∗
         ((coroPtr + 0x718#64) ↦₆₄ kyberKpPubPtr) ∗ ((coroPtr + 0x720#64) ↦₆₄ 0x620#64) ∗
         ((coroPtr + 0x741#64) ↦ₛ opkPkBytes) ∗
         opkUnusedFieldAt (coroPtr + 0x761#64) inp.opkBSk? opkSkBytes ∗
         memRegion (coroPtr + 0x798#64) 64 ∗ ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
         ((msgPtr + 0xa8#64) ↦ₛ bytesToBv8 inp.hdr.ekAPk) ∗
         ((msgPtr + 0xc8#64) ↦ₛ bytesToBv8 inp.hdr.ikAPk) ∗
         protocolAddressAt A.repAlloc gMe localAddrPtr ∗
         protocolAddressAt A.repAlloc gPeer remoteAddrPtr ∗
         cells (sp + 0x560#64) 4 ∗ cells (sp + 0x6a0#64) 4 ∗ cells (sp + 0x7e0#64) 4 ∗
         cells (sp + 0x930#64) 8 ∗ cells (sp + 0xa90#64) 8 ∗
         (lsLogFilterAddr ↦₆₄ 0#64) ∗ anyHeap ∗ A.pool lim (M.stepEvents evs st) sf ∗
         stackAt sp stk ∗ F_rest) Q Qp) :
    SepWPp (stageP1ProgPlaced ext) (s0.readReg64 .x30) s6
      (((coroPtr + 0x798#64) ↦₆₄ ik0) ∗ ((coroPtr + 0x7a0#64) ↦₆₄ ik1) ∗
       ((coroPtr + 0x7a8#64) ↦₆₄ ik2) ∗ ((coroPtr + 0x7b0#64) ↦₆₄ ik3) ∗
       ((coroPtr + 0x7b8#64) ↦₆₄ ik4) ∗ ((coroPtr + 0x7c0#64) ↦₆₄ ik5) ∗
       ((coroPtr + 0x7c8#64) ↦₆₄ ik6) ∗ ((coroPtr + 0x7d0#64) ↦₆₄ ik7) ∗
       ((coroPtr + 0x398#64) ↦ₛ bytesToBv8 spkBPk) ∗ ((coroPtr + 0x3b8#64) ↦ₛ bytesToBv8 inp.spkBSk) ∗
       ((coroPtr + 0x3d8#64) ↦₆₄ kyberKpPubPtr) ∗ ((coroPtr + 0x3e0#64) ↦₆₄ 0x620#64) ∗
       ((coroPtr + 0x3e8#64) ↦₆₄ kyberKpSecPtr) ∗ ((coroPtr + 0x3f0#64) ↦₆₄ 0xc60#64) ∗
       ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗ ((coroPtr + 0x470#64) ↦₆₄ remoteAddrPtr) ∗
       ((coroPtr + 0x478#64) ↦₆₄ localAddrPtr) ∗ ((coroPtr + 0x488#64) ↦₆₄ (msgPtr + 0x90#64)) ∗
       ((coroPtr + 0x4b0#64) ↦₆₄ opk0) ∗ ((coroPtr + 0x4b8#64) ↦₆₄ opk1) ∗ ((coroPtr + 0x4c0#64) ↦₆₄ opk2) ∗
       ((coroPtr + 0x4c8#64) ↦₆₄ opk3) ∗ ((coroPtr + 0x4d0#64) ↦₆₄ opk4) ∗ ((coroPtr + 0x4d8#64) ↦₆₄ opk5) ∗
       ((coroPtr + 0x4e0#64) ↦₆₄ opk6) ∗ ((coroPtr + 0x4e8#64) ↦₆₄ opk7) ∗
       ((coroPtr + 0x4f0#64) ↦₈ opk_b64) ∗ ((coroPtr + 0x4f1#64) ↦₈ b_4f1) ∗
       memRegion (coroPtr + 0x658#64) 298 ∗ ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
       ((msgPtr + 0x90#64) ↦₆₄ ctBufPtr) ∗ ((msgPtr + 0x98#64) ↦₆₄ BitVec.ofNat 64 ctBytes.length) ∗
       ((msgPtr + 0xa8#64) ↦ₛ bytesToBv8 inp.hdr.ekAPk) ∗ ((msgPtr + 0xc8#64) ↦ₛ bytesToBv8 inp.hdr.ikAPk) ∗
       (kyberKpSecPtr ↦₈ (bytesToBv8 inp.pqspkBSk).getD 0 0#8) ∗
       ((kyberKpSecPtr + 1#64) ↦ₛ (bytesToBv8 inp.pqspkBSk).drop 1) ∗
       (ctBufPtr ↦ₛ ctBytes) ∗
       protocolAddressAt A.repAlloc gMe localAddrPtr ∗ protocolAddressAt A.repAlloc gPeer remoteAddrPtr ∗
       memRegion (sp + 0x3e0#64) 65 ∗ memRegion (sp + 0x421#64) 279 ∗
       ((sp + 0x930#64) ↦₆₄ ik0) ∗ ((sp + 0x938#64) ↦₆₄ ik1) ∗
       ((sp + 0x940#64) ↦₆₄ ik2) ∗ ((sp + 0x948#64) ↦₆₄ ik3) ∗
       ((sp + 0x950#64) ↦₆₄ u_950) ∗ ((sp + 0x958#64) ↦₆₄ u_958) ∗
       ((sp + 0x960#64) ↦₆₄ u_960) ∗ ((sp + 0x968#64) ↦₆₄ u_968) ∗
       cells (sp + 0x560#64) 4 ∗ cells (sp + 0x6a0#64) 4 ∗ cells (sp + 0x7e0#64) 4 ∗
       cells (sp + 0xa90#64) 8 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool lim st s6 ∗ stackAt sp stk ∗ F_rest)
      Q Qp := by
  have hstk_le64 : stk ≤ 2 ^ 64 := Nat.le_trans hstk_lt (Nat.le_of_lt sp.isLt)
  have hikBPk_bv : (bytesToBv8 ikBPk).length = 32 := by
    rw [bytesToBv8_length]; exact hikBPk_len
  have hspkBPk_bv : (bytesToBv8 spkBPk).length = 32 := by
    rw [bytesToBv8_length]; exact hspkBPk_len
  have hspkBSk_bv : (bytesToBv8 inp.spkBSk).length = 32 := by
    rw [bytesToBv8_length]; exact hwell.2.2.1
  have hikAPk_bv : (bytesToBv8 inp.hdr.ikAPk).length = 32 := by
    rw [bytesToBv8_length]; exact hwell.2.2.2.2.2.2.2.1
  have hekAPk_bv : (bytesToBv8 inp.hdr.ekAPk).length = 32 := by
    rw [bytesToBv8_length]; exact hwell.2.2.2.2.2.2.2.2.1
  obtain ⟨spk0, spk1, spk2, spk3, hspkPk⟩ := exists_words4_of_len32 hspkBPk_bv
  obtain ⟨spk4, spk5, spk6, spk7, hspkSk⟩ := exists_words4_of_len32 hspkBSk_bv
  obtain ⟨ikA0, ikA1, ikA2, ikA3, hikA⟩ := exists_words4_of_len32 hikAPk_bv
  obtain ⟨ekA0, ekA1, ekA2, ekA3, hekA⟩ := exists_words4_of_len32 hekAPk_bv
  have hspk_398 :
      ((coroPtr + 0x398#64) ↦ₛ bytesToBv8 spkBPk) ∗
        ((coroPtr + 0x3b8#64) ↦ₛ bytesToBv8 inp.spkBSk) =
      ((coroPtr + 0x398#64) ↦₆₄ spk0) ∗ ((coroPtr + 0x3a0#64) ↦₆₄ spk1) ∗
      ((coroPtr + 0x3a8#64) ↦₆₄ spk2) ∗ ((coroPtr + 0x3b0#64) ↦₆₄ spk3) ∗
      ((coroPtr + 0x3b8#64) ↦₆₄ spk4) ∗ ((coroPtr + 0x3c0#64) ↦₆₄ spk5) ∗
      ((coroPtr + 0x3c8#64) ↦₆₄ spk6) ∗ ((coroPtr + 0x3d0#64) ↦₆₄ spk7) := by
    rw [hspkPk (coroPtr + 0x398#64), hspkSk (coroPtr + 0x3b8#64)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  have hekA_msg : ((msgPtr + 0xa8#64) ↦ₛ bytesToBv8 inp.hdr.ekAPk) =
      ((msgPtr + 0xa8#64) ↦₆₄ ekA0) ∗ ((msgPtr + 0xb0#64) ↦₆₄ ekA1) ∗
      ((msgPtr + 0xb8#64) ↦₆₄ ekA2) ∗ ((msgPtr + 0xc0#64) ↦₆₄ ekA3) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using hekA (msgPtr + 0xa8#64)
  have hikA_msg : ((msgPtr + 0xc8#64) ↦ₛ bytesToBv8 inp.hdr.ikAPk) =
      ((msgPtr + 0xc8#64) ↦₆₄ ikA0) ∗ ((msgPtr + 0xd0#64) ↦₆₄ ikA1) ∗
      ((msgPtr + 0xd8#64) ↦₆₄ ikA2) ∗ ((msgPtr + 0xe0#64) ↦₆₄ ikA3) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using hikA (msgPtr + 0xc8#64)
  refine CryptoVerification.E2E.Pqxdh.ResponderClosure.SepWPp.weaken_frame (Entails.of_eq hspk_398) (by sep_focus) ?_
  refine CryptoVerification.E2E.Pqxdh.ResponderClosure.SepWPp.weaken_frame (Entails.of_eq hekA_msg) (by sep_focus) ?_
  refine CryptoVerification.E2E.Pqxdh.ResponderClosure.SepWPp.weaken_frame (Entails.of_eq hikA_msg) (by sep_focus) ?_
  refine CryptoVerification.E2E.Pqxdh.ResponderClosure.SepWPp.weaken_frame (Entails.of_eq (memRegion65_eq_words8_byte (sp + 0x3e0#64)))
    (by sep_focus) ?_
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun u_420 => SepWPp.exists_elim fun u_3e0 =>
    SepWPp.exists_elim fun u_3e8 => SepWPp.exists_elim fun u_3f0 =>
    SepWPp.exists_elim fun u_3f8 => SepWPp.exists_elim fun u_400 =>
    SepWPp.exists_elim fun u_408 => SepWPp.exists_elim fun u_410 =>
    SepWPp.exists_elim fun u_418 => ?_
  have hca90 : cells (sp + 0xa90#64) 8 =
      (∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 64, ∃∗ u3 : BitVec 64,
       ∃∗ u4 : BitVec 64, ∃∗ u5 : BitVec 64, ∃∗ u6 : BitVec 64, ∃∗ u7 : BitVec 64,
        ((sp + 0xa90#64) ↦₆₄ u0) ∗ ((sp + 0xa98#64) ↦₆₄ u1) ∗
        ((sp + 0xaa0#64) ↦₆₄ u2) ∗ ((sp + 0xaa8#64) ↦₆₄ u3) ∗
        ((sp + 0xab0#64) ↦₆₄ u4) ∗ ((sp + 0xab8#64) ↦₆₄ u5) ∗
        ((sp + 0xac0#64) ↦₆₄ u6) ∗ ((sp + 0xac8#64) ↦₆₄ u7)) := by
    simp only [cells, BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine CryptoVerification.E2E.Pqxdh.ResponderClosure.SepWPp.weaken_frame (Entails.of_eq hca90) (by sep_focus) ?_
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun u_a90 => SepWPp.exists_elim fun u_a98 =>
    SepWPp.exists_elim fun u_aa0 => SepWPp.exists_elim fun u_aa8 =>
    SepWPp.exists_elim fun u_ab0 => SepWPp.exists_elim fun u_ab8 =>
    SepWPp.exists_elim fun u_ac0 => SepWPp.exists_elim fun u_ac8 => ?_
  have hc560 : cells (sp + 0x560#64) 4 =
      (∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 64, ∃∗ u3 : BitVec 64,
        ((sp + 0x560#64) ↦₆₄ u0) ∗ ((sp + 0x568#64) ↦₆₄ u1) ∗
        ((sp + 0x570#64) ↦₆₄ u2) ∗ ((sp + 0x578#64) ↦₆₄ u3)) := by
    simp only [cells, BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine CryptoVerification.E2E.Pqxdh.ResponderClosure.SepWPp.weaken_frame (Entails.of_eq hc560) (by sep_focus) ?_
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun u_560 => SepWPp.exists_elim fun u_568 =>
    SepWPp.exists_elim fun u_570 => SepWPp.exists_elim fun u_578 => ?_
  have hc6a0 : cells (sp + 0x6a0#64) 4 =
      (∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 64, ∃∗ u3 : BitVec 64,
        ((sp + 0x6a0#64) ↦₆₄ u0) ∗ ((sp + 0x6a8#64) ↦₆₄ u1) ∗
        ((sp + 0x6b0#64) ↦₆₄ u2) ∗ ((sp + 0x6b8#64) ↦₆₄ u3)) := by
    simp only [cells, BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine CryptoVerification.E2E.Pqxdh.ResponderClosure.SepWPp.weaken_frame (Entails.of_eq hc6a0) (by sep_focus) ?_
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun u_6a0 => SepWPp.exists_elim fun u_6a8 =>
    SepWPp.exists_elim fun u_6b0 => SepWPp.exists_elim fun u_6b8 => ?_
  have hc7e0 : cells (sp + 0x7e0#64) 4 =
      (∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 64, ∃∗ u3 : BitVec 64,
        ((sp + 0x7e0#64) ↦₆₄ u0) ∗ ((sp + 0x7e8#64) ↦₆₄ u1) ∗
        ((sp + 0x7f0#64) ↦₆₄ u2) ∗ ((sp + 0x7f8#64) ↦₆₄ u3)) := by
    simp only [cells, BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine CryptoVerification.E2E.Pqxdh.ResponderClosure.SepWPp.weaken_frame (Entails.of_eq hc7e0) (by sep_focus) ?_
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun u_7e0 => SepWPp.exists_elim fun u_7e8 =>
    SepWPp.exists_elim fun u_7f0 => SepWPp.exists_elim fun u_7f8 => ?_
  have hsp6_align : (s6.sp &&& 15#64 == 0#64) = true := by rw [hsp6]; exact hsp_align
  have hstep7 := p2_seg5c3_ext_placed_wp ext s6 coroPtr msgPtr localAddrPtr remoteAddrPtr
    ik4 ik5 ik6 ik7
    spk0 spk1 spk2 spk3 spk4 spk5 spk6 spk7
    opk0 opk1 opk2 opk3 opk4 opk5 opk6 opk7
    kyberKpPubPtr 0x620#64 kyberKpSecPtr 0xc60#64
    ikA0 ikA1 ikA2 ikA3
    ekA0 ekA1 ekA2 ekA3
    u_950 u_958 u_960 u_968
    u_a90 u_a98 u_aa0 u_aa8 u_ab0 u_ab8 u_ac0 u_ac8
    u_3e0 u_3e8 u_3f0 u_3f8 u_400 u_408 u_410 u_418
    u_560 u_568 u_570 u_578
    u_6a0 u_6a8 u_6b0 u_6b8
    u_7e0 u_7e8 u_7f0 u_7f8
    opk_b64 u_420 b_4f1
    hpc6 hrun6 hsp6_align
    hx0_6 hx1_6 hx2_6 hx3_6
    hx8_6 hx9_6 hx10_6 hx19_6
    (by rw [hx22_6, hsp6]) (by rw [hx23_6, hsp6]) hx24_6 (by rw [hx28_6, hsp6])
  rw [hsp6] at hstep7
  refine p2_bind_sepWP_steps_memInv_sub5_qpan hInv hCode6
    (by simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using hstep7)
    (by sep_focus)
    fun s7 hst67 hpc7 hrun7 hCode7 hregs7 => ?_
  rcases hregs7 with ⟨hsp7_6, htr7_6, hx0_7, hx1_7, hx2_7, hx3_7, hx19_7, hx21_7, hx22_7, hx23_7,
    hx24_7, hx25_7, hx26_7, _, hx28_7, hx29_7, hx30_7, hvregs7_6, hvm7_6⟩
  have hsp7 : s7.sp = sp := hsp7_6
  have hsp7_al : s7.spAligned = true := by simpa only [State.spAligned, hsp7] using hsp_align
  refine CryptoVerification.E2E.Pqxdh.ResponderClosure.SepWPp.weaken_frame (Entails.of_eq (A.pool_of_vmPreserved hvm7_6).symm) (by sep_focus) ?_
  let localIk : IdentityKey := ⟨⟨⟨bytesToBv8 ikBPk, hikBPk_bv⟩⟩⟩
  let remoteIk : IdentityKey := ⟨⟨⟨bytesToBv8 inp.hdr.ikAPk, hikAPk_bv⟩⟩⟩
  have hneq' : localIk ≠ remoteIk ∨ DistinctSid uuidTryParse gMe.name.bytes gPeer.name.bytes :=
    hneq.imp (fun h => identityKey_ne_of_bytes_ne hikBPk_bv hikAPk_bv h) id
  have hlocIk_eq : ((coroPtr + 0x798#64) ↦₆₄ ik0) ∗ ((coroPtr + 0x7a0#64) ↦₆₄ ik1) ∗
      ((coroPtr + 0x7a8#64) ↦₆₄ ik2) ∗ ((coroPtr + 0x7b0#64) ↦₆₄ ik3) =
      ((coroPtr + 0x798#64) ↦ₛ localIk.publicKey.bytes.toList) := by
    change _ = ((coroPtr + 0x798#64) ↦ₛ bytesToBv8 ikBPk)
    simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
      (hikB0 (coroPtr + 0x798#64)).symm
  have hremIk_eq : ((msgPtr + 0xc8#64) ↦₆₄ ikA0) ∗ ((msgPtr + 0xd0#64) ↦₆₄ ikA1) ∗
      ((msgPtr + 0xd8#64) ↦₆₄ ikA2) ∗ ((msgPtr + 0xe0#64) ↦₆₄ ikA3) =
      ((msgPtr + 0xc8#64) ↦ₛ remoteIk.publicKey.bytes.toList) :=
    hikA_msg.symm
  refine CryptoVerification.E2E.Pqxdh.ResponderClosure.SepWPp.weaken_frame (Entails.of_eq hlocIk_eq) (by sep_focus) ?_
  refine CryptoVerification.E2E.Pqxdh.ResponderClosure.SepWPp.weaken_frame (Entails.of_eq hremIk_eq) (by sep_focus) ?_
  have hstk_same := p2_stackAt_split_of_le sp stk sameStk
    hsame_le hstk_le64
  refine CryptoVerification.E2E.Pqxdh.ResponderClosure.SepWPp.weaken_frame (Entails.of_eq hstk_same) (by sep_focus) ?_
  have hpc7_eq :
      libsignalSessionLib.resolve lsmpl
        "<libsignal_protocol::identity_key::IdentityKey>::is_same_account" = lsmpl.base 17 :=
    BitVec.add_zero _
  rw [hpc7_eq] at hpc7
  refine p2_call_nopanic_lscl_steps_frame_placed
    (x := (coroPtr + 0x798#64, localIk, localAddrPtr, gMe,
           msgPtr + 0xc8#64, remoteIk, remoteAddrPtr, gPeer))
    (R_pure := s7.readReg64 .x0 = coroPtr + 0x798#64 ∧ s7.readReg64 .x1 = localAddrPtr ∧
          s7.readReg64 .x2 = msgPtr + 0xc8#64 ∧ s7.readReg64 .x3 = remoteAddrPtr ∧
          (localIk ≠ remoteIk ∨ DistinctSid uuidTryParse gMe.name.bytes gPeer.name.bytes))
    (T := ((coroPtr + 0x798#64) ↦ₛ localIk.publicKey.bytes.toList) ∗
          protocolAddressAt A.repAlloc gMe localAddrPtr ∗
          ((msgPtr + 0xc8#64) ↦ₛ remoteIk.publicKey.bytes.toList) ∗
          protocolAddressAt A.repAlloc gPeer remoteAddrPtr ∗ stackAt sp sameStk)
    (hInv.toCodeRo hCode7) hSameAcct hpc7 hrun7 hsp7_al hx30_7
    (by
      dsimp only [isSameAccountDistinctAtSpec, withVmPreserved,
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits.isSameAccountDistinctAtSpec]
      rw [hsp7])
    ⟨hx0_7, hx1_7, hx2_7, hx3_7, hneq'⟩ (by sep_focus)
    (hnext := fun s8 hst78 hpc8 hrun8 hsp8_7 _ hcs8 _ => ?_)
  have hCode8 : Φ s8.mem := hInv.of_keepsFrozen hCode7 hst78.keepsFrozen
  dsimp only [isSameAccountDistinctAtSpec, withVmPreserved,
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits.isSameAccountDistinctAtSpec]
  rw [hsp7]
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun hvm8_7 => ?_
  refine SepWPp.pure_elim fun ⟨hx0_8_lo, htr8_7⟩ => ?_
  refine CryptoVerification.E2E.Pqxdh.ResponderClosure.SepWPp.weaken_frame (Entails.of_eq (A.pool_of_vmPreserved hvm8_7).symm) (by sep_focus) ?_
  have hsp8 : s8.sp = sp := hsp8_7.trans hsp7
  have hsp8_align : (s8.sp &&& 15#64 == 0#64) = true := by rw [hsp8]; exact hsp_align
  rcases hcs8 with ⟨hx19_cs8, _, hx21_cs8, hx22_cs8, hx23_cs8, hx24_cs8, hx25_cs8, hx26_cs8, _,
    hx28_cs8, hx29_cs8, hvregscs8⟩
  have hx19_8 : s8.readReg64 .x19 = coroPtr := hx19_cs8.trans hx19_7
  have hx21_8 : s8.readReg64 .x21 = msgPtr + 0x90#64 := by rw [hx21_cs8, hx21_7, hx21_6]
  have hx22_8 : s8.readReg64 .x22 = s8.sp + 0x370#64 := by rw [hx22_cs8, hx22_7, hsp8]
  have hx23_8 : s8.readReg64 .x23 = s8.sp + 0x930#64 := by rw [hx23_cs8, hx23_7, hsp8]
  have hx24_8 : s8.readReg64 .x24 = coroPtr + 0x398#64 := hx24_cs8.trans hx24_7
  have hx25_8 : s8.readReg64 .x25 = s6.readReg64 .x25 := hx25_cs8.trans hx25_7
  have hx26_8 : s8.readReg64 .x26 = s6.readReg64 .x26 := hx26_cs8.trans hx26_7
  have hx28_8 : s8.readReg64 .x28 = s8.sp + 0xa90#64 := by rw [hx28_cs8, hx28_7, hsp8]
  have hx29_8 : s8.readReg64 .x29 = fp := by rw [hx29_cs8, hx29_7, hx29_6]
  refine CryptoVerification.E2E.Pqxdh.ResponderClosure.SepWPp.weaken_frame (Entails.of_eq hstk_same.symm) (by sep_focus) ?_
  refine CryptoVerification.E2E.Pqxdh.ResponderClosure.SepWPp.weaken_frame (Entails.of_eq hlocIk_eq.symm) (by sep_focus) ?_
  have hremIk_fold : ((msgPtr + 0xc8#64) ↦ₛ remoteIk.publicKey.bytes.toList) =
      ((msgPtr + 0xc8#64) ↦ₛ bytesToBv8 inp.hdr.ikAPk) := rfl
  refine CryptoVerification.E2E.Pqxdh.ResponderClosure.SepWPp.weaken_frame (Entails.of_eq hremIk_fold) (by sep_focus) ?_
  have h798_64 : ((coroPtr + 0x798#64) ↦₆₄ ik0) ∗ ((coroPtr + 0x7a0#64) ↦₆₄ ik1) ∗
      ((coroPtr + 0x7a8#64) ↦₆₄ ik2) ∗ ((coroPtr + 0x7b0#64) ↦₆₄ ik3) ∗
      ((coroPtr + 0x7b8#64) ↦₆₄ ik4) ∗ ((coroPtr + 0x7c0#64) ↦₆₄ ik5) ∗
      ((coroPtr + 0x7c8#64) ↦₆₄ ik6) ∗ ((coroPtr + 0x7d0#64) ↦₆₄ ik7) ⊢
      memRegion (coroPtr + 0x798#64) 64 := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
      words8_entails_memRegion64 (coroPtr + 0x798#64) ik0 ik1 ik2 ik3 ik4 ik5 ik6 ik7
  refine CryptoVerification.E2E.Pqxdh.ResponderClosure.SepWPp.weaken_frame h798_64 (by sep_focus) ?_
  refine CryptoVerification.E2E.Pqxdh.ResponderClosure.SepWPp.weaken_frame (Entails.of_eq hspk_398.symm) (by sep_focus) ?_
  have hopk_4b0_symm :
      ((coroPtr + 0x4b0#64) ↦₆₄ opk0) ∗ ((coroPtr + 0x4b8#64) ↦₆₄ opk1) ∗
      ((coroPtr + 0x4c0#64) ↦₆₄ opk2) ∗ ((coroPtr + 0x4c8#64) ↦₆₄ opk3) ∗
      ((coroPtr + 0x4d0#64) ↦₆₄ opk4) ∗ ((coroPtr + 0x4d8#64) ↦₆₄ opk5) ∗
      ((coroPtr + 0x4e0#64) ↦₆₄ opk6) ∗ ((coroPtr + 0x4e8#64) ↦₆₄ opk7) ∗
      ((coroPtr + 0x4f0#64) ↦₈ opk_b64) =
      ((coroPtr + 0x4b0#64) ↦₈ opkPresentTag inp.opkBSk?) ∗ ((coroPtr + 0x4b1#64) ↦ₛ opkPkBytes) ∗
      ((coroPtr + 0x4d1#64) ↦ₛ opkSkBytes) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
      (hopk (coroPtr + 0x4b0#64)).symm
  refine CryptoVerification.E2E.Pqxdh.ResponderClosure.SepWPp.weaken_frame (Entails.of_eq hopk_4b0_symm) (by sep_focus) ?_
  refine CryptoVerification.E2E.Pqxdh.ResponderClosure.SepWPp.weaken_frame (Entails.of_eq hekA_msg.symm) (by sep_focus) ?_
  refine CryptoVerification.E2E.Pqxdh.ResponderClosure.SepWPp.weaken_frame (Entails.of_eq (coro658_298_eq coroPtr)) (by sep_focus) ?_
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun c_781 => SepWPp.exists_elim fun c_780 => ?_
  have hc658 : cells (coroPtr + 0x658#64) 37 =
      (∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64, ∃∗ c2 : BitVec 64, ∃∗ c3 : BitVec 64, ∃∗ c4 : BitVec 64, ∃∗ c5 : BitVec 64,
       ∃∗ c6 : BitVec 64, ∃∗ c7 : BitVec 64, ∃∗ c8 : BitVec 64, ∃∗ c9 : BitVec 64, ∃∗ c10 : BitVec 64, ∃∗ c11 : BitVec 64,
       ∃∗ c12 : BitVec 64, ∃∗ c13 : BitVec 64, ∃∗ c14 : BitVec 64, ∃∗ c15 : BitVec 64, ∃∗ c16 : BitVec 64, ∃∗ c17 : BitVec 64,
       ∃∗ c18 : BitVec 64, ∃∗ c19 : BitVec 64, ∃∗ c20 : BitVec 64, ∃∗ c21 : BitVec 64, ∃∗ c22 : BitVec 64, ∃∗ c23 : BitVec 64,
       ∃∗ c24 : BitVec 64, ∃∗ c25 : BitVec 64, ∃∗ c26 : BitVec 64, ∃∗ c27 : BitVec 64, ∃∗ c28 : BitVec 64, ∃∗ c29 : BitVec 64,
       ∃∗ c30 : BitVec 64, ∃∗ c31 : BitVec 64, ∃∗ c32 : BitVec 64, ∃∗ c33 : BitVec 64, ∃∗ c34 : BitVec 64, ∃∗ c35 : BitVec 64, ∃∗ c36 : BitVec 64,
        ((coroPtr + 0x658#64) ↦₆₄ c0) ∗ ((coroPtr + 0x660#64) ↦₆₄ c1) ∗ ((coroPtr + 0x668#64) ↦₆₄ c2) ∗
        ((coroPtr + 0x670#64) ↦₆₄ c3) ∗ ((coroPtr + 0x678#64) ↦₆₄ c4) ∗ ((coroPtr + 0x680#64) ↦₆₄ c5) ∗
        ((coroPtr + 0x688#64) ↦₆₄ c6) ∗ ((coroPtr + 0x690#64) ↦₆₄ c7) ∗ ((coroPtr + 0x698#64) ↦₆₄ c8) ∗
        ((coroPtr + 0x6a0#64) ↦₆₄ c9) ∗ ((coroPtr + 0x6a8#64) ↦₆₄ c10) ∗ ((coroPtr + 0x6b0#64) ↦₆₄ c11) ∗
        ((coroPtr + 0x6b8#64) ↦₆₄ c12) ∗ ((coroPtr + 0x6c0#64) ↦₆₄ c13) ∗ ((coroPtr + 0x6c8#64) ↦₆₄ c14) ∗
        ((coroPtr + 0x6d0#64) ↦₆₄ c15) ∗ ((coroPtr + 0x6d8#64) ↦₆₄ c16) ∗ ((coroPtr + 0x6e0#64) ↦₆₄ c17) ∗
        ((coroPtr + 0x6e8#64) ↦₆₄ c18) ∗ ((coroPtr + 0x6f0#64) ↦₆₄ c19) ∗ ((coroPtr + 0x6f8#64) ↦₆₄ c20) ∗
        ((coroPtr + 0x700#64) ↦₆₄ c21) ∗ ((coroPtr + 0x708#64) ↦₆₄ c22) ∗ ((coroPtr + 0x710#64) ↦₆₄ c23) ∗
        ((coroPtr + 0x718#64) ↦₆₄ c24) ∗ ((coroPtr + 0x720#64) ↦₆₄ c25) ∗ ((coroPtr + 0x728#64) ↦₆₄ c26) ∗
        ((coroPtr + 0x730#64) ↦₆₄ c27) ∗ ((coroPtr + 0x738#64) ↦₆₄ c28) ∗ ((coroPtr + 0x740#64) ↦₆₄ c29) ∗
        ((coroPtr + 0x748#64) ↦₆₄ c30) ∗ ((coroPtr + 0x750#64) ↦₆₄ c31) ∗ ((coroPtr + 0x758#64) ↦₆₄ c32) ∗
        ((coroPtr + 0x760#64) ↦₆₄ c33) ∗ ((coroPtr + 0x768#64) ↦₆₄ c34) ∗ ((coroPtr + 0x770#64) ↦₆₄ c35) ∗
        ((coroPtr + 0x778#64) ↦₆₄ c36)) := by
    simp (config := { maxSteps := 1000000 }) only
      [cells, BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp,
       sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine CryptoVerification.E2E.Pqxdh.ResponderClosure.SepWPp.weaken_frame (Entails.of_eq hc658) (by sep_focus) ?_
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun c_658 => SepWPp.exists_elim fun c_660 => SepWPp.exists_elim fun c_668 =>
    SepWPp.exists_elim fun c_670 => SepWPp.exists_elim fun c_678 => SepWPp.exists_elim fun c_680 =>
    SepWPp.exists_elim fun c_688 => SepWPp.exists_elim fun c_690 => SepWPp.exists_elim fun c_698 =>
    SepWPp.exists_elim fun c_6a0 => SepWPp.exists_elim fun c_6a8 => SepWPp.exists_elim fun c_6b0 =>
    SepWPp.exists_elim fun c_6b8 => SepWPp.exists_elim fun c_6c0 => SepWPp.exists_elim fun c_6c8 =>
    SepWPp.exists_elim fun c_6d0 => SepWPp.exists_elim fun c_6d8 => SepWPp.exists_elim fun c_6e0 =>
    SepWPp.exists_elim fun c_6e8 => SepWPp.exists_elim fun c_6f0 => SepWPp.exists_elim fun c_6f8 =>
    SepWPp.exists_elim fun c_700 => SepWPp.exists_elim fun c_708 => SepWPp.exists_elim fun c_710 =>
    SepWPp.exists_elim fun c_718 => SepWPp.exists_elim fun c_720 => SepWPp.exists_elim fun c_728 =>
    SepWPp.exists_elim fun c_730 => SepWPp.exists_elim fun c_738 => SepWPp.exists_elim fun c_740 =>
    SepWPp.exists_elim fun c_748 => SepWPp.exists_elim fun c_750 => SepWPp.exists_elim fun c_758 =>
    SepWPp.exists_elim fun c_760 => SepWPp.exists_elim fun c_768 => SepWPp.exists_elim fun c_770 =>
    SepWPp.exists_elim fun c_778 => ?_
  have hstep9 := p2_seg5d_ext_placed_wp ext s8 coroPtr (msgPtr + 0x90#64) (s8.readReg64 .x0)
    ik0 ik1 ik2 ik3 ik4 ik5 ik6 ik7 spk0 spk1 spk2 spk3 spk4 spk5 spk6 spk7
    opk0 opk1 opk2 opk3 opk4 opk5 opk6 opk7 kyberKpPubPtr 0x620#64 kyberKpSecPtr 0xc60#64
    ikA0 ikA1 ikA2 ikA3 ekA0 ekA1 ekA2 ekA3
    c_658 c_660 c_668 c_670 c_678 c_680 c_688 c_690 c_698 c_6a0 c_6a8 c_6b0 c_6b8 c_6c0 c_6c8 c_6d0
    c_6d8 c_6e0 c_6e8 c_6f0 c_6f8 c_700 c_708 c_710 c_718 c_720 c_728 c_730 c_738
    c_740 c_748 c_750 c_758 c_760 c_768 c_770 c_778 opk_b64 c_780 c_781
    hpc8 hrun8 hsp8_align rfl hx19_8 hx21_8 hx22_8 hx23_8 hx24_8 hx28_8
  have hx0_8_b : (s8.readReg64 .x0).setWidth 8 = 0#8 := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    have h0 := congrArg (fun v => v.getLsbD i) hx0_8_lo
    have hi32 : i < 32 := by omega
    simpa [BitVec.getLsbD_setWidth, hi, hi32] using h0
  rw [hsp8, hx0_8_b] at hstep9
  refine p2_bind_sepWP_steps_memInv_sub5_qpan hInv hCode8
    (by simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using hstep9)
    (by sep_focus)
    fun s9 hst89 hpc9 hrun9 hCode9 hregs9 => ?_
  rcases hregs9 with ⟨hsp9_8, htr9_8, hx0_9, hx1_9, hx8_9, hx19_9, hx21_9, hx22_9, hx23_9, hx24_9,
    hx25_9, hx26_9, _, hx28_9, hx29_9, hx30_9, hvregs9_8, hvm9_8⟩
  have hsp9 : s9.sp = sp := hsp9_8
  have hsp9_al : s9.spAligned = true := by simpa only [State.spAligned, hsp9] using hsp_align
  refine CryptoVerification.E2E.Pqxdh.ResponderClosure.SepWPp.weaken_frame (Entails.of_eq (A.pool_of_vmPreserved hvm9_8).symm) (by sep_focus) ?_
  refine CryptoVerification.E2E.Pqxdh.ResponderClosure.SepWPp.weaken_frame
    (words8_byte_entails_memRegion65 (sp + 0x3e0#64) opk0 opk1 opk2 opk3 opk4 opk5 opk6 opk7
      opk_b64)
    (by sep_focus) ?_
  refine CryptoVerification.E2E.Pqxdh.ResponderClosure.SepWPp.weaken_frame (Entails.of_eq (sp3e0_344_split_65_279 sp).symm) (by sep_focus) ?_
  refine CryptoVerification.E2E.Pqxdh.ResponderClosure.SepWPp.weaken_frame (by
      simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
        words8_entails_cells8 (sp + 0x930#64) ik0 ik1 ik2 ik3 ik4 ik5 ik6 ik7)
    (by sep_focus) ?_
  refine CryptoVerification.E2E.Pqxdh.ResponderClosure.SepWPp.weaken_frame (by
      simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
        words8_entails_cells8 (sp + 0xa90#64) spk0 spk1 spk2 spk3 spk4 spk5 spk6 spk7)
    (by sep_focus) ?_
  refine CryptoVerification.E2E.Pqxdh.ResponderClosure.SepWPp.weaken_frame (by
      simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
        words4_entails_cells4 (sp + 0x560#64) kyberKpPubPtr 0x620#64 kyberKpSecPtr 0xc60#64)
    (by sep_focus) ?_
  refine CryptoVerification.E2E.Pqxdh.ResponderClosure.SepWPp.weaken_frame (by
      simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
        words4_entails_cells4 (sp + 0x6a0#64) ikA0 ikA1 ikA2 ikA3)
    (by sep_focus) ?_
  refine CryptoVerification.E2E.Pqxdh.ResponderClosure.SepWPp.weaken_frame (by
      simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
        words4_entails_cells4 (sp + 0x7e0#64) ekA0 ekA1 ekA2 ekA3)
    (by sep_focus) ?_
  have hikB0_658 : ((coroPtr + 0x658#64) ↦₆₄ ik0) ∗ ((coroPtr + 0x660#64) ↦₆₄ ik1) ∗
      ((coroPtr + 0x668#64) ↦₆₄ ik2) ∗ ((coroPtr + 0x670#64) ↦₆₄ ik3) =
      ((coroPtr + 0x658#64) ↦ₛ bytesToBv8 ikBPk) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
      (hikB0 (coroPtr + 0x658#64)).symm
  have hikB1_678 : ((coroPtr + 0x678#64) ↦₆₄ ik4) ∗ ((coroPtr + 0x680#64) ↦₆₄ ik5) ∗
      ((coroPtr + 0x688#64) ↦₆₄ ik6) ∗ ((coroPtr + 0x690#64) ↦₆₄ ik7) =
      ((coroPtr + 0x678#64) ↦ₛ bytesToBv8 inp.ikBSk) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
      (hikB1 (coroPtr + 0x678#64)).symm
  have hspkPk_698 : ((coroPtr + 0x698#64) ↦₆₄ spk0) ∗ ((coroPtr + 0x6a0#64) ↦₆₄ spk1) ∗
      ((coroPtr + 0x6a8#64) ↦₆₄ spk2) ∗ ((coroPtr + 0x6b0#64) ↦₆₄ spk3) =
      ((coroPtr + 0x698#64) ↦ₛ bytesToBv8 spkBPk) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
      (hspkPk (coroPtr + 0x698#64)).symm
  have hspkSk_6b8 : ((coroPtr + 0x6b8#64) ↦₆₄ spk4) ∗ ((coroPtr + 0x6c0#64) ↦₆₄ spk5) ∗
      ((coroPtr + 0x6c8#64) ↦₆₄ spk6) ∗ ((coroPtr + 0x6d0#64) ↦₆₄ spk7) =
      ((coroPtr + 0x6b8#64) ↦ₛ bytesToBv8 inp.spkBSk) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
      (hspkSk (coroPtr + 0x6b8#64)).symm
  have hikA_6d8 : ((coroPtr + 0x6d8#64) ↦₆₄ ikA0) ∗ ((coroPtr + 0x6e0#64) ↦₆₄ ikA1) ∗
      ((coroPtr + 0x6e8#64) ↦₆₄ ikA2) ∗ ((coroPtr + 0x6f0#64) ↦₆₄ ikA3) =
      ((coroPtr + 0x6d8#64) ↦ₛ bytesToBv8 inp.hdr.ikAPk) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
      (hikA (coroPtr + 0x6d8#64)).symm
  have hekA_6f8 : ((coroPtr + 0x6f8#64) ↦₆₄ ekA0) ∗ ((coroPtr + 0x700#64) ↦₆₄ ekA1) ∗
      ((coroPtr + 0x708#64) ↦₆₄ ekA2) ∗ ((coroPtr + 0x710#64) ↦₆₄ ekA3) =
      ((coroPtr + 0x6f8#64) ↦ₛ bytesToBv8 inp.hdr.ekAPk) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
      (hekA (coroPtr + 0x6f8#64)).symm
  have hopk_740 : ((coroPtr + 0x740#64) ↦₆₄ opk0) ∗ ((coroPtr + 0x748#64) ↦₆₄ opk1) ∗
      ((coroPtr + 0x750#64) ↦₆₄ opk2) ∗ ((coroPtr + 0x758#64) ↦₆₄ opk3) ∗
      ((coroPtr + 0x760#64) ↦₆₄ opk4) ∗ ((coroPtr + 0x768#64) ↦₆₄ opk5) ∗
      ((coroPtr + 0x770#64) ↦₆₄ opk6) ∗ ((coroPtr + 0x778#64) ↦₆₄ opk7) ∗
      ((coroPtr + 0x780#64) ↦₈ opk_b64) =
      ((coroPtr + 0x740#64) ↦₈ opkPresentTag inp.opkBSk?) ∗ ((coroPtr + 0x741#64) ↦ₛ opkPkBytes) ∗
      ((coroPtr + 0x761#64) ↦ₛ opkSkBytes) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
      (hopk (coroPtr + 0x740#64)).symm
  refine CryptoVerification.E2E.Pqxdh.ResponderClosure.SepWPp.weaken_frame (Entails.of_eq hikB0_658) (by sep_focus) ?_
  refine CryptoVerification.E2E.Pqxdh.ResponderClosure.SepWPp.weaken_frame (Entails.of_eq hikB1_678) (by sep_focus) ?_
  refine CryptoVerification.E2E.Pqxdh.ResponderClosure.SepWPp.weaken_frame (Entails.of_eq hspkPk_698) (by sep_focus) ?_
  refine CryptoVerification.E2E.Pqxdh.ResponderClosure.SepWPp.weaken_frame (Entails.of_eq hspkSk_6b8) (by sep_focus) ?_
  refine CryptoVerification.E2E.Pqxdh.ResponderClosure.SepWPp.weaken_frame (Entails.of_eq hikA_6d8) (by sep_focus) ?_
  refine CryptoVerification.E2E.Pqxdh.ResponderClosure.SepWPp.weaken_frame (Entails.of_eq hekA_6f8) (by sep_focus) ?_
  refine CryptoVerification.E2E.Pqxdh.ResponderClosure.SepWPp.weaken_frame (Entails.of_eq hopk_740) (by sep_focus) ?_
  refine CryptoVerification.E2E.Pqxdh.ResponderClosure.SepWPp.weaken_frame
    (Entails.of_eq (opkSlot65_eq_optField (coroPtr + 0x761#64) inp.opkBSk? opkSkBytes hopkSk_eq))
    (by sep_focus) ?_
  refine CryptoVerification.E2E.Pqxdh.ResponderClosure.SepWPp.weaken_frame
    (Entails.of_eq (bobParamsBadKemFieldsAt_intro coroPtr msgPtr kyberKpSecPtr ctBufPtr inp ctBytes ikBPk spkBPk))
    (by sep_focus) ?_
  have htr9_6 : s9.trace = s6.trace := by rw [htr9_8, htr8_7, htr7_6]
  have hvregs9 : calleeSavedVRegs s9 = calleeSavedVRegs s0 := by
    rw [hvregs9_8, hvregscs8, hvregs7_6, hvregs6]
  have hpc9_eq :
      libsignalSessionLib.resolve lsmpl
        "libsignal_protocol::ratchet::initialize_bob_session" = lsmpl.base 75 :=
    BitVec.add_zero _
  rw [hpc9_eq] at hpc9
  have hstk_err := p2_stackAt_split_of_le sp stk (768 + pqxdhEntryStack) herr_le hstk_le64
  refine CryptoVerification.E2E.Pqxdh.ResponderClosure.SepWPp.weaken_frame (Entails.of_eq hstk_err) (by sep_focus) ?_
  refine p2_call_memInv_nopanic_steps_frame_sub5 hInv
    (x := (({ inp := inp, ctBytes := ctBytes, ikBPk := ikBPk, spkBPk := spkBPk,
              sameAccountByte := 0#8, argPtr := coroPtr + 1624#64, pqskPtr := kyberKpSecPtr,
              ctSlicePtr := msgPtr + 144#64, ctBufPtr := ctBufPtr,
              ratchetKeyPairPtr := coroPtr + 920#64, outPtr := sp + 992#64 } : InitBobBadKemGhost), st))
    (φ := s9.readReg64 .x0 = coroPtr + 1624#64 ∧ s9.readReg64 .x1 = coroPtr + 920#64 ∧
          s9.readReg64 .x8 = sp + 992#64 ∧ inp.trustedPeer = true ∧ inp.replayOk = true ∧
          inp.hdr.opkId?.isSome = inp.opkBSk?.isSome ∧ WellSizedAcceptKeysInput inp ∧
          ikBPk.length = 32 ∧ spkBPk.length = 32 ∧ ctBytes.length < 2 ^ 63 ∧
          pkVecTag? 8#8 1568 ctBytes = none ∧ FitsEnv M lim st (AcceptErrEnv inp))
    (T := bobParamsBadKemFieldsAt (coroPtr + 1624#64) kyberKpSecPtr (msgPtr + 144#64) ctBufPtr
            (coroPtr + 920#64) inp ctBytes ikBPk spkBPk 0#8 ∗ memRegion (sp + 992#64) 344 ∗
          (lsLogFilterAddr ↦₆₄ 0#64) ∗ stackAt sp (768 + pqxdhEntryStack) ∗ A.pool lim st s9)
    hCode9 hInitBobBadKemErrOwned hpc9 hrun9 hsp9_al hx30_9
    (by dsimp only [LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemBobAuxPlacedBudget.initializeBobSessionBadKemErrOwnedInnerPlacedSpec]; rw [hsp9])
    ⟨hx0_9, hx1_9, hx8_9, htrusted, hreplay, hopk_match, hwell, hikBPk_len, hspkBPk_len,
     hct_bd, hbadKem, hfits_err⟩
    (by sep_focus)
    (hnext := fun sf hst9f hpcf hrunf hspf_9 _ hcsf hCodef => ?_)
  dsimp only [LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemBobAuxPlacedBudget.initializeBobSessionBadKemErrOwnedInnerPlacedSpec]
  rw [hsp9]
  simp only [sepConj_assoc]
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun evs => ?_
  refine SepWPp.pure_elim fun ⟨htrf_9, hevsErr⟩ => ?_
  rcases hcsf with ⟨hx19_csf, _, hx21_csf, hx22_csf, hx23_csf, hx24_csf, hx25_csf, hx26_csf, _,
    hx28_csf, hx29_csf, hvregscsf⟩
  refine CryptoVerification.E2E.Pqxdh.ResponderClosure.SepWPp.weaken_frame (Entails.of_eq hstk_err.symm) (by sep_focus) ?_
  refine CryptoVerification.E2E.Pqxdh.ResponderClosure.SepWPp.weaken_frame (LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemP2KitsPlacedBudget.p2_initBobBadKemErrOwnedAt_unpack A sp) (by sep_focus) ?_
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun errTag => SepWPp.exists_elim fun w2 =>
    SepWPp.exists_elim fun w3 => SepWPp.exists_elim fun w4 =>
    SepWPp.exists_elim fun w5 => SepWPp.exists_elim fun w6 => ?_
  refine SepWPp.pure_elim fun ⟨herr_ne2, herr_ne3⟩ => ?_
  have hsteps_all := hst67.trans (hst78.trans (hst89.trans hst9f))
  have herr := hErrBob evs errTag w2 w3 w4 w5 w6 sf hevsErr herr_ne2 herr_ne3
    hsteps_all hpcf hrunf (hspf_9.trans hsp9) (htrf_9.trans htr9_6)
    (hx19_csf.trans hx19_9) (hx21_csf.trans hx21_9) (hx22_csf.trans hx22_9)
    (hx23_csf.trans hx23_9) (hx24_csf.trans hx24_9)
    (by rw [hx25_csf, hx25_9, hx25_8]) (by rw [hx26_csf, hx26_9, hx26_8])
    (hx28_csf.trans hx28_9) (by rw [hx29_csf, hx29_9, hx29_8])
    (hvregscsf.trans hvregs9) (hInv.toCodeRo hCodef)
  exact p2_sepWPp_weaken_eq herr (by sep_focus)

end LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemP2TopSub5APlacedBudget
