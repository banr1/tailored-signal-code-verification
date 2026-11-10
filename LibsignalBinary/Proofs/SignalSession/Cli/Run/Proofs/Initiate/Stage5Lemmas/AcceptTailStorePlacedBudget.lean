/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCalleesPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.AcceptTailStorePlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.CallKitPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.EpiloguePlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.ScratchAndStoreCallsPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage2Lemmas.HelpersPlaced
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.ModelBridge
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.SessionBridge
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice

/-!
# Budget-Threaded Stage 5 Accept Path (`[LibsignalPlacement]`): `store_session` and Post-Store Cleanup

Verifies `store_session` and post-store cleanup (`+0x1768 → +0x0350 → lr`) on `initProgPlaced W`
under `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false
set_option linter.dupNamespace false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

noncomputable section

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.AcceptTailStorePlacedBudget

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.ProgramReflection CryptoGames
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreKit CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.RecordCodecs
open CryptoVerification.E2E
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet hiding
  withLsCodeRoLoaded extract_withLsCodeRoLoaded subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.CodeLayout
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs hiding initSlotSpecPlaced
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage2Lemmas
  (sepWPp_weaken_pre sepWPp_pure_left sepWPp_exists_left)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage5Lemmas hiding
  s5_call_raw_placed s5_dealloc_ok_at_placed s5_memcpy_ok_at_placed s5_call_futDrop_placed
  s5_call_dealloc_placed s5_call_dropSS_placed
  stage5_epilogue_placed_ok stage5_err_cleanup_placed_ok
  stage5_cleanup_after_store_placed_ok stage5_store_and_cleanup_placed_ok
open CryptoVerification.CliHandshake.InitiatePlaced
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget VmPreserved
   rustDeallocEvents)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (BoxAllocEnv futDropBudgetSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsXCliPlaced sessStoreShimSpecPlaced sessStorePollSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.DefsPlacedBudget
  (InitExitPostPlaced initSlotSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.CallKitPlacedBudget
  (s5_call_raw_placed s5_call_futDrop_pool_placed s5_call_dealloc_placed s5_call_dropSS_placed
   s5_dealloc_ok_at_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.EpiloguePlacedBudget
  (sepWPp_step_to_lscro_vm_mem stage5_epilogue_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.ScratchAndStoreCallsPlacedBudget
  (s5_call_sessStoreShim_placed s5_call_sessStorePoll_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (CliGhostHooks cliGhostExterns)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm] BitVec.toNat_zero
attribute [-arm64_norm, -wp_norm] fsp_stage5_eqs
attribute [-arm64_norm]
  CryptoVerification.LibsignalTripleRatchet.Expand.sp_sub_496_eq_esp
  CryptoVerification.LibsignalTripleRatchet.Expand.sp_add_neg496_eq_esp
  CryptoVerification.LibsignalTripleRatchet.Expand.esp_add_496_sub_496
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_sub_592_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_neg592_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_add_688_sub_688
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_96_eq_sp

@[local arm64_norm, local wp_norm]
private theorem fsp_compound_offs_placed (fsp : BitVec 64) :
    fsp + 0xe0#64 + 8#64 = fsp + 0xe8#64 ∧ fsp + 0xf0#64 + 8#64 = fsp + 0xf8#64 ∧
    fsp + 0xf8#64 + 8#64 = fsp + 0x100#64 ∧ fsp + 0x100#64 + 8#64 = fsp + 0x108#64 ∧
    fsp + 0x130#64 + 8#64 = fsp + 0x138#64 ∧
    fsp + 0x80#64 + 168#64 = fsp + 0x128#64 ∧ fsp + 0x80#64 + 192#64 = fsp + 0x140#64 ∧
    fsp + 0x80#64 + 536#64 = fsp + 0x298#64 ∧ fsp + 0x460#64 + 0x154#64 = fsp + 0x5b4#64 ∧
    fsp + 4096#64 + 1536#64 = fsp + 0x1600#64 :=
  ⟨by bv_omega, by bv_omega, by bv_omega, by bv_omega, by bv_omega,
   by bv_omega, by bv_omega, by bv_omega, by bv_omega, by bv_omega⟩

private theorem sepWP_done_tpidr {prog : Program} {target_pc : BitVec 64} {s0 s : State}
    {P : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = target_pc) (hrun : s.status = .Running)
    (htp : s.tpidrEl0 = s0.tpidrEl0) (hpost : Q s P) :
    SepWP prog target_pc s P (fun sm Pm => sm.tpidrEl0 = s0.tpidrEl0 ∧ Q sm Pm) :=
  SepWP.done hpc hrun ⟨htp, hpost⟩

private theorem s5_apply_lens_oom {prog : Program} {ret : BitVec 64} {s : State}
    {L P Rest : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (heq : P = L ∗ Rest)
    (h : ∀ R (m : Memory), m ⊨ L ∗ R → ∃ B : SepProp, m ⊨ B ∗ R ∧
      SepWPp prog ret s (B ∗ Rest) Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  intro R hm hL
  rw [heq, sepConj_assoc] at hm
  obtain ⟨B, hmB, hw⟩ := h (Rest ∗ R) s.mem hm
  rw [← sepConj_assoc] at hmB
  exact hw R hmB hL

private theorem s5_with_rodata_oom {prog : Program} {ret : BitVec 64} {s : State}
    {RO P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hro : ∀ {X : SepProp}, s.mem ⊨ X → s.mem ⊨ (RO ∗ X))
    (hw : SepWPp prog ret s (RO ∗ P) Q Qp oom) :
    SepWPp prog ret s P Q Qp oom :=
  fun R hm hL => hw R (by rw [sepConj_assoc]; exact hro hm) hL

/-- Framed variant of `sepWPp_step_to_lscro_vm_mem` so `wp_steps` only traverses `P₀` while
    carrying `VmPreserved s (sm.setMem m)` to transport `A.pool lim st` in `F`. -/
theorem sepWPp_step_to_lscro_vm_mem_framed {prog : Program} {pl : MultiPlacement}
    {ret mid : BitVec 64} {s sm : State} {P P₀ Pm F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hcrl : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded pl s.mem) (hsplit : P = P₀ ∗ F)
    (hstep : SepWP prog mid s P₀
      (fun s' P' => VmPreserved s s' ∧ (∃ m, s' = sm.setMem m) ∧ P' = Pm))
    (hcont : ∀ m, VmPreserved s (sm.setMem m) →
      LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded pl (sm.setMem m).mem →
      SepWPp prog ret (sm.setMem m) (Pm ∗ F) Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  subst hsplit
  refine sepWPp_step_to_lscro_vm_mem (mid := mid) hcrl ?_ hcont
  unfold SepWP at hstep ⊢; intro R hm hL
  rw [sepConj_assoc] at hm
  obtain ⟨sf, hsteps, hout⟩ := hstep (F ∗ R) hm hL
  refine ⟨sf, hsteps, ?_⟩
  rcases hout with ⟨hpc, hrun, Pf, hmf, hvmp, hmEq, rfl⟩ | ⟨_, hfalse⟩
  · exact Or.inl ⟨hpc, hrun, Pf ∗ F, by rw [sepConj_assoc]; exact hmf, hvmp, hmEq, rfl⟩
  · exact (not_satisfies_false_sepConj hfalse).elim

private theorem saveUpd_own_eq_placed (rd : ReadRule) (F : FsFiles) (g : IdGhost)
    (peer : AddrVal) (key : IdentityKey) :
    (g.saveUpd rd F peer key).own = g.own := by
  unfold IdGhost.saveUpd; split <;> rfl

/-! ## Minimal-Frame Decomposition -/

private def initArgsStoreRestPlaced [LibsignalPlacement] (fsp : BitVec 64) (x : InitGhost)
    (s0 : State) : SepProp :=
  ((fsp + 0xd8#64) ↦₆₄ x.meA) ∗
    ((fsp + 0xf0#64) ↦₆₄ x.stores) ∗
    ((fsp + 0xf8#64) ↦₆₄ lsρ cliIdentityVtSym) ∗
    ((fsp + 0x100#64) ↦₆₄ x.bundleA) ∗
    ((fsp + 0x108#64) ↦₆₄ 0#64) ∗
    ((fsp + 0x110#64) ↦₃₂ 0#32) ∗ memRegion (fsp + 0x114#64) 4 ∗
    ((fsp + 0x118#64) ↦₆₄ (s0.sp - 0x71#64)) ∗
    ((fsp + 0x120#64) ↦₆₄ (x.bundleA + 0x78#64))

private theorem initArgsAtPlaced_store_split [LibsignalPlacement] (fsp : BitVec 64) (x : InitGhost)
    (s0 : State) :
    initArgsAtPlaced fsp x s0 =
      (((fsp + 0xd0#64) ↦₆₄ x.peerA) ∗
        ((fsp + 0xe0#64) ↦₆₄ (x.stores + 0xf0#64)) ∗
        ((fsp + 0xe8#64) ↦₆₄ lsρ cliSessionVtSym)) ∗
      initArgsStoreRestPlaced fsp x s0 := by
  dsimp only [initArgsAtPlaced, initArgsStoreRestPlaced]; ac_rfl

private def stage5ScratchRestPlaced (fsp w5d0 : BitVec 64) : SepProp :=
  memRegion (fsp + 0x5ba#64) 6 ∗
    ((fsp + 0x5d0#64) ↦₆₄ w5d0) ∗
    memRegion (fsp + 0x5d8#64) (0x1600 - 0x5d8) ∗
    memRegion (fsp + 0x1630#64) 296 ∗
    memRegion (fsp + 0x1758#64) (initLocalsSize - 0x1758)

private theorem stage5ScratchAt_store_split_placed (fsp w5c0 w5c8 w5d0 : BitVec 64) :
    stage5ScratchAt fsp w5c0 w5c8 w5d0 =
      (((fsp + 0x5c0#64) ↦₆₄ w5c0) ∗
        ((fsp + 0x5c8#64) ↦₆₄ w5c8) ∗
        memRegion (fsp + 0x1600#64) 48) ∗
      stage5ScratchRestPlaced fsp w5d0 := by
  dsimp only [stage5ScratchAt, stage5ScratchRestPlaced]; ac_rfl

private def stage3KeySlotsRestPlaced (fsp : BitVec 64) (b : BundleV) (kp : IdentityKeyPair)
    (ekASk ekAPk : List (BitVec 8)) (opkId : BitVec 32) : SepProp :=
  ((fsp + 0x298#64) ↦ₛ ekAPk) ∗
    memRegion (fsp + 0x2b8#64) 0x48 ∗
    ((fsp + 0x300#64) ↦₃₂ (if b.opk.isSome then 1#32 else 0#32)) ∗
    ((fsp + 0x304#64) ↦₃₂ opkId) ∗
    memRegion (fsp + 0x308#64) 0x40 ∗
    ((fsp + 0x348#64) ↦ₛ kp.identityKey.publicKey.bytes.toList) ∗
    ((fsp + 0x368#64) ↦ₛ kp.privateKey.bytes.toList) ∗
    ((fsp + 0x388#64) ↦ₛ ekAPk) ∗
    ((fsp + 0x3a8#64) ↦ₛ ekASk) ∗
    ((fsp + 0x3c8#64) ↦ₛ b.idKey.publicKey.bytes.toList) ∗
    ((fsp + 0x3e8#64) ↦ₛ b.spk.bytes.toList) ∗
    ((fsp + 0x408#64) ↦ₛ b.spk.bytes.toList) ∗
    ((fsp + 0x438#64) ↦₈ (if b.opk.isSome then 1#32 else 0#32).truncate 8) ∗
    stage3OpkSlotAt fsp b ∗
    ((fsp + 0x459#64) ↦₈ 0#8) ∗
    memRegion (fsp + 0x45a#64) 6

private theorem stage3KeySlotsAt_dealloc_split_placed {M : AllocCostModel}
    (A : RustCliAllocBudget M) (fsp : BitVec 64) (b : BundleV)
    (kp : IdentityKeyPair) (ekASk ekAPk : List (BitVec 8))
    (pqspkPtr : BitVec 64) (opkId : BitVec 32) :
    stage3KeySlotsAt A.repAlloc fsp b kp ekASk ekAPk pqspkPtr opkId =
      (((fsp + 0x428#64) ↦₆₄ pqspkPtr) ∗ ((fsp + 0x430#64) ↦₆₄ 1568#64) ∗
        A.live pqspkPtr 1568 1 ∗ (pqspkPtr ↦ₛ b.kpk)) ∗
      stage3KeySlotsRestPlaced fsp b kp ekASk ekAPk opkId := by
  rw [stage3KeySlotsAt_unfold]; dsimp only [stage3KeySlotsRestPlaced]; ac_rfl

private theorem collapse_initLocals_from_rest_placed [LibsignalPlacement] (fsp : BitVec 64)
    {x : InitGhost} {kp : IdentityKeyPair} {ekASk ekAPk : List (BitVec 8)}
    {pqspkPtr : BitVec 64} {opkId : BitVec 32} {s0 : State}
    (w128 w130 w138 : BitVec 64) (b5b8 b5b9 : BitVec 8)
    (hekLen : ekASk.length = 32 ∧ ekAPk.length = 32) :
    memRegion fsp 0xd0 ∗ initArgsAtPlaced fsp x s0 ∗
      ((fsp + 0x128#64) ↦₆₄ w128) ∗ ((fsp + 0x130#64) ↦₆₄ w130) ∗ ((fsp + 0x138#64) ↦₆₄ w138) ∗
      memRegion (fsp + 0x140#64) 344 ∗
      ((fsp + 0x428#64) ↦₆₄ pqspkPtr) ∗ ((fsp + 0x430#64) ↦₆₄ 1568#64) ∗
      stage3KeySlotsRestPlaced fsp x.bundle kp ekASk ekAPk opkId ∗
      memRegion (fsp + 0x460#64) 344 ∗
      ((fsp + 0x5b8#64) ↦₈ b5b8) ∗ ((fsp + 0x5b9#64) ↦₈ b5b9) ∗
      memRegion (fsp + 0x5ba#64) (initLocalsSize - 0x5ba) ⊢
      memRegion fsp initLocalsSize := by
  refine Entails.trans ?_
    (collapse_initLocals_placed fsp (x := x) (kp := kp)
      (pqspkPtr := pqspkPtr) (opkId := opkId) (s0 := s0)
      w128 w130 w138 b5b8 b5b9 hekLen)
  dsimp only [stage3KeySlotsRestPlaced]
  exact Entails.of_eq (by s5_ac_rfl)

private theorem stage5_dealloc_and_drop_rec_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    [InitTraceFsSound mmpl gh W]
    {B : RunBudgets} {pqspkPtr : BitVec 64} {kpk : List (BitVec 8)}
    {sg₂ : SessionGhost} {sess : Session (List (BitVec 8))}
    {st : M.σ} {Rest : SepProp} {stk : Nat} {s0 s : State}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hAlloc : AllocContractsXCliPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hDropSS : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 512)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget.dropSessionStructureLocal2Spec
          M A lim)))
    (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hkpkLen : kpk.length = 1568)
    (hpc : s.pc = initEntryPlaced + offStoreDeallocDone)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - BitVec.ofNat 64 cliInitiateFrame)
    (hsp_align : s0.spAligned = true)
    (hinv : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hx26 : s.readReg64 (.gpr 26#5) = 0xFFFFFFFFFFFFFFFE#64)
    (hnext : ∀ (sm : State) (evsDrop : List AllocEvent),
      FreeOnlyEvs evsDrop →
      sm.pc = initEntryPlaced + offEpilogue →
      sm.status = .Running →
      sm.sp = s0.sp - BitVec.ofNat 64 cliInitiateFrame →
      calleeSavedVRegs sm = calleeSavedVRegs s →
      LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem →
      sm.trace = s0.trace →
      sm.fs.files = s.fs.files →
      sm.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) →
      sm.readReg64 (.gpr 26#5) = 0xFFFFFFFFFFFFFFFE#64 →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sm
        ((((s0.sp - BitVec.ofNat 64 cliInitiateFrame + 0x128#64) ↦₆₄ 0#64) ∗
          ((s0.sp - BitVec.ofNat 64 cliInitiateFrame + 0x130#64) ↦₆₄ 8#64) ∗
          ((s0.sp - BitVec.ofNat 64 cliInitiateFrame + 0x138#64) ↦₆₄ 0#64) ∗
          memRegion (s0.sp - BitVec.ofNat 64 cliInitiateFrame + 0x140#64) 344 ∗
          ((s0.sp - BitVec.ofNat 64 cliInitiateFrame + 0x428#64) ↦₆₄ pqspkPtr) ∗
          ((s0.sp - BitVec.ofNat 64 cliInitiateFrame + 0x430#64) ↦₆₄ 1568#64) ∗
          ((s0.sp - BitVec.ofNat 64 cliInitiateFrame + 0x5b9#64) ↦₈ 0#8) ∗
          A.pool lim (M.stepEvents evsDrop (M.stepEvents (rustDeallocEvents 1568 1) st)) sm ∗
          stackAt (s0.sp - BitVec.ofNat 64 cliInitiateFrame) (stk - cliInitiateFrame)) ∗ Rest)
        Q Qp oom) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s
      ((sessionRecordAt A.repAlloc (fsp + 0x128#64) ⟨0#64, 8#64, some sg₂⟩ ⟨some sess⟩ ∗
        ((fsp + 0x428#64) ↦₆₄ pqspkPtr) ∗ ((fsp + 0x430#64) ↦₆₄ 1568#64) ∗
        A.live pqspkPtr 1568 1 ∗ (pqspkPtr ↦ₛ kpk) ∗
        ((fsp + 0x5b9#64) ↦₈ 0#8) ∗ A.pool lim st s ∗
        stackAt fsp (stk - cliInitiateFrame)) ∗ Rest) Q Qp oom := by
  intro fsp
  have hDealloc := s5_dealloc_ok_at_placed hAlloc
  have halign_s : s.spAligned = true := spAligned_fsp hsp_align hsp
  change s.sp = fsp at hsp
  conv => arg 4; simp only [sepConj_assoc]
  s5_have_eq hpStep5 :
      (((fsp + 0x430#64) ↦₆₄ 1568#64) ∗ ((fsp + 0x5b9#64) ↦₈ 0#8) ∗
        ((fsp + 0x428#64) ↦₆₄ pqspkPtr)) ∗ ?remStep5 := by
    s5_ac_rfl
  rw [initEntryPlaced_eq_blkPl] at hpc
  apply sepWPp_step_to_lscro_vm_mem_framed hinv hpStep5 (mid := lsρ lsRustDeallocSymCli)
  · dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521, offStoreDeallocDone, lsρ] at hpc ⊢
    by_vm_steps (
      wp_steps
      simp (config := { failIfUnchanged := false }) only [hx26]
      try wp_steps
      apply sepWP_done_tpidr (by wp_norm_goal) (by wp_norm_lhs)
        (by simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm])
      exact ⟨state_exists_setMem _, rfl⟩)
  intro _ hvmp5 hinv5; clear hpStep5
  have hkpkMem : (pqspkPtr ↦ₛ kpk) ⊢ memRegion pqspkPtr 1568 := by
    simpa [hkpkLen] using pointsToBytes_entails_memRegion pqspkPtr kpk
  conv =>
    arg 4
    rw [s5_stackAt_sub_split fsp (extHook_le_stkSub hstk) (stkSub_hi hstk64)]
    simp only [sepConj_assoc]
  refine s5_call_dealloc_placed (s0 := s0) (ret_pc := initEntryPlaced + offOkAfterDealloc)
    hDealloc fsp pqspkPtr 1568 1 st ?stF5
    (by dsimp only [lsρ]; wp_norm_goal; try rfl) (by wp_norm_lhs)
    (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, hsp])
    (by simpa [State.spAligned, wp_norm, arm64_norm] using halign_s)
    (by dsimp only [initEntryPlaced, offOkAfterDealloc]; wp_norm_goal; try rfl)
    (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, htr]) hinv5
    (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) ⟨layoutOk_1568_1, by decide⟩
    ?stPre5 ?_
  case stPre5 =>
    rw [A.pool_of_vmPreserved hvmp5]
    s5_have_eq hpull : (pqspkPtr ↦ₛ kpk) ∗ ?restKpk := by
      conv => lhs; simp (config := { zetaDelta := false, failIfUnchanged := false }) only [BitVec.add_zero, hsp]
      s5_ac_rfl
    refine Entails.trans (Entails.of_eq hpull)
      (Entails.trans (sepConj_mono_left hkpkMem) ?_)
    s5_close_frame
  intro sm5 hpc5 hrun5 hsp5 hal5 hcs5 hinv5 htr5 hfs5
  simp (config := { zetaDelta := false }) only [CalleeSavedPreserved, wp_norm, arm64_norm, hx26] at hcs5
  rcases hcs5 with ⟨hx19_5, _, _, _, _, _, _, hx26_5, _, _, _, hvregs_5⟩
  s5_rw_pre (s5_stackAt_sub_split fsp (extHook_le_stkSub hstk) (stkSub_hi hstk64)).symm
  s5_have_eq hpRecEq :
      sessionRecordAt A.repAlloc (fsp + 0x128#64) ⟨0#64, 8#64, some sg₂⟩ ⟨some sess⟩ ∗ ?recRem := by
    s5_ac_rfl
  refine s5_apply_lens_oom hpRecEq fun R m hm => ?_
  obtain ⟨capRec, RecRest, hcapRecNe, hmRec, hfoldRecSS⟩ :=
    sessionRecord_unpack_drop A.repAlloc fsp sg₂ sess R m hm
  simp only [← sepConj_assoc] at hmRec
  refine ⟨_, hmRec, ?_⟩
  conv => arg 4; simp only [sepConj_assoc]
  s5_have_eq hpStep6 : ((fsp + 0x140#64) ↦₆₄ capRec) ∗ ?remStep6 := by s5_ac_rfl
  rw [initEntryPlaced_eq_blkPl] at hpc5
  apply sepWPp_step_to_lscro_vm_mem_framed hinv5 hpStep6 (mid := lsmpl.base 512)
  · dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521, offOkAfterDealloc] at hpc5 ⊢
    by_vm_steps (
      wp_steps
      simp (config := { failIfUnchanged := false }) only [beq_eq_false_iff_ne.mpr hcapRecNe,
        Bool.false_eq_true, ↓reduceIte]
      try wp_steps
      apply sepWP_done_tpidr (by wp_norm_goal) (by wp_norm_lhs)
        (by simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm])
      exact ⟨state_exists_setMem _, rfl⟩)
  intro _ hvmp6 hinv6; clear hpStep6
  conv =>
    arg 4
    rw [s5_stackAt_sub_split fsp (dropSS_le_stkSub hstk) (stkSub_hi hstk64)]
    simp only [sepConj_assoc]
  refine s5_call_dropSS_placed (s0 := s0) (ret_pc := initEntryPlaced + offOkAfterDrop)
    hDropSS fsp (fsp + 0x140#64) sg₂ sess.state (M.stepEvents (rustDeallocEvents 1568 1) st) ?stF6
    (by wp_norm_goal; try rfl) (by wp_norm_lhs)
    (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, hsp5])
    (by simpa [State.spAligned, wp_norm, arm64_norm] using hal5)
    (by dsimp only [initEntryPlaced, offOkAfterDrop]; wp_norm_goal; try rfl)
    (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, htr5]) hinv6
    (by wp_norm_goal)
    ?stPre6 ?_
  case stPre6 =>
    rw [A.pool_of_vmPreserved hvmp6]
    s5_have_eq hpull : (((fsp + 0x140#64) ↦₆₄ capRec) ∗ RecRest) ∗ ?restDrop := by
      conv => lhs; simp (config := { zetaDelta := false, failIfUnchanged := false }) only [BitVec.add_zero, hsp5]
      s5_ac_rfl
    refine Entails.trans (Entails.of_eq hpull)
      (Entails.trans (sepConj_mono_left hfoldRecSS) ?_)
    s5_close_frame
  intro sm6 evsDrop hfreeDrop hpc6 hrun6 hsp6 hal6 hcs6 hinv6 htr6 hfs6
  have hfs6' : sm6.fs.files = s.fs.files := hfs6.trans hfs5
  simp (config := { zetaDelta := false }) only [CalleeSavedPreserved, wp_norm, arm64_norm, hx19_5, hx26_5, hvregs_5] at hcs6
  rcases hcs6 with ⟨hx19_6, _, _, _, _, _, _, hx26_6, _, _, _, hvregs_6⟩
  s5_rw_pre (s5_stackAt_sub_split fsp (dropSS_le_stkSub hstk) (stkSub_hi hstk64)).symm
  conv => arg 4; simp only [sepConj_assoc]
  s5_have_eq hpStep7 :
      (((fsp + 0x128#64) ↦₆₄ 0#64) ∗ ((fsp + 0x130#64) ↦₆₄ 8#64) ∗
        ((fsp + 0x138#64) ↦₆₄ 0#64)) ∗ ?remStep7 := by
    s5_ac_rfl
  rw [initEntryPlaced_eq_blkPl] at hpc6
  apply sepWPp_step_to_lscro_vm_mem_framed hinv6 hpStep7 (mid := initEntryPlaced + offEpilogue)
  · dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521, offOkAfterDrop, offEpilogue] at hpc6 ⊢
    rw [initEntryPlaced_eq_blkPl]
    by_vm_steps (
      wp_steps
      apply sepWP_done_tpidr (by wp_norm_goal) (by wp_norm_lhs)
        (by simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm])
      exact ⟨state_exists_setMem _, rfl⟩)
  intro m7 hvmp7 hinv7; clear hpStep7
  refine sepWPp_weaken_pre ?_
    (hnext _ evsDrop hfreeDrop
      (by dsimp only [initEntryPlaced, offEpilogue]; wp_norm_goal; try rfl)
      (by wp_norm_lhs)
      (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm]; exact hsp6)
      (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, hvregs_6])
      hinv7
      (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, htr6])
      hfs6'
      (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, hx19_6])
      (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, hx26_6]))
  rw [A.pool_of_vmPreserved hvmp7]
  conv => lhs; simp (config := { zetaDelta := false, failIfUnchanged := false }) only [BitVec.add_zero]
  exact Entails.of_eq (by dsimp only [fsp]; s5_ac_rfl)

private theorem stage5_store_shim_poll_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {StoreEnv : SessStorePollGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    [InitTraceFsSound mmpl gh W]
    {x : InitGhost} {sg₂ : SessionGhost}
    {sess : Session (List (BitVec 8))} {w5c0 w5c8 : BitVec 64}
    {st : M.σ} {Rest : SepProp} {stk : Nat}
    {s0 s : State} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hRodataStoreSlot : ∀ {m : Memory} {P : SepProp},
      LibsignalRoLoaded lsmpl m → (m ⊨ P) →
        (m ⊨ ((lsρ cliSessionVtSym + 32#64) ↦₆₄ᵣ lsmpl.base 605) ∗ P))
    (hShim : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 605)
      (sessStoreShimSpecPlaced A lim (stk - cliInitiateFrame)))
    (hPoll : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 570)
      (sessStorePollSpecPlaced A lim StoreEnv (stk - cliInitiateFrame)))
    (hFitShim : FitsEnv M lim st (BoxAllocEnv 32))
    (hFitPoll : ∀ (fut : BitVec 64) (evsShim : List AllocEvent),
      BoxAllocEnv 32 evsShim →
      FitsEnv M lim (M.stepEvents evsShim st)
        (StoreEnv
          { call :=
              { call :=
                  { addrA := x.peerA
                    addr := x.peer
                    recA := s0.sp - BitVec.ofNat 64 cliInitiateFrame + 0x128#64
                    g := ⟨0#64, 8#64, some sg₂⟩
                    record := ⟨some sess⟩ }
                fut := fut
                out := s0.sp - BitVec.ofNat 64 cliInitiateFrame + 0x1600#64 }
            self := x.stores + 0xf0#64
            dir := StoresGhost.opened.sessions }))
    (hnameLt : x.peer.name.bytes.length < 2 ^ 32)
    (hencLt : (Record.encodeRecord ⟨some sess⟩).length < 2 ^ 32)
    (hpc : s.pc = initEntryPlaced + offStore) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - BitVec.ofNat 64 cliInitiateFrame) (hsp_align : s0.spAligned = true)
    (hinv : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s.mem) (htr : s.trace = s0.trace)
    (hx21 : s.readReg64 (.gpr 21#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x80#64)
    (hnext : ∀ (sm : State) (fut : BitVec 64) (evsShim evsPoll : List AllocEvent) (JunkRO : SepProp),
      BoxAllocEnv 32 evsShim →
      StoreEnv
        { call :=
            { call :=
                { addrA := x.peerA
                  addr := x.peer
                  recA := s0.sp - BitVec.ofNat 64 cliInitiateFrame + 0x128#64
                  g := ⟨0#64, 8#64, some sg₂⟩
                  record := ⟨some sess⟩ }
              fut := fut
              out := s0.sp - BitVec.ofNat 64 cliInitiateFrame + 0x1600#64 }
          self := x.stores + 0xf0#64
          dir := StoresGhost.opened.sessions } evsPoll →
      sm.pc = initEntryPlaced + offAfterStorePoll →
      sm.status = .Running →
      sm.sp = s0.sp - BitVec.ofNat 64 cliInitiateFrame →
      calleeSavedVRegs sm = calleeSavedVRegs s →
      LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem →
      sm.trace = s0.trace →
      sm.fs.files = s.fs.files →
      sm.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sm
        ((let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
          A.live fut 32 8 ∗
          sessStoreBoxAt fut (x.stores + 0xf0#64) x.peerA (fsp + 0x128#64) 1#8 ∗
          dirAt A.repAlloc (x.stores + 0xf0#64)
            (StoresGhost.opened.sessions.put (addressText x.peer.val)
              (E2E.Record.encodeRecord ⟨some sess⟩)) ∗
          ((fsp + 0x1600#64) ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗
          memRegion ((fsp + 0x1600#64) + 8#64) 40 ∗
          protocolAddressAt A.repAlloc x.peer x.peerA ∗
          sessionRecordAt A.repAlloc (fsp + 0x128#64) ⟨0#64, 8#64, some sg₂⟩ ⟨some sess⟩ ∗
          ((fsp + 0xd0#64) ↦₆₄ x.peerA) ∗
          ((fsp + 0xe0#64) ↦₆₄ (x.stores + 0xf0#64)) ∗
          ((fsp + 0xe8#64) ↦₆₄ lsρ cliSessionVtSym) ∗
          ((fsp + 0x5c0#64) ↦₆₄ fut) ∗
          ((fsp + 0x5c8#64) ↦₆₄ lsρ sessStoreFutVtSym) ∗
          A.pool lim (M.stepEvents evsPoll (M.stepEvents evsShim st)) sm ∗
          stackAt fsp (stk - cliInitiateFrame)) ∗ Rest ∗ JunkRO) Q Qp oom) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s
      ((((fsp + 0xd0#64) ↦₆₄ x.peerA) ∗
        ((fsp + 0xe0#64) ↦₆₄ (x.stores + 0xf0#64)) ∗
        ((fsp + 0xe8#64) ↦₆₄ lsρ cliSessionVtSym) ∗
        dirAt A.repAlloc (x.stores + 0xf0#64) StoresGhost.opened.sessions ∗
        protocolAddressAt A.repAlloc x.peer x.peerA ∗
        sessionRecordAt A.repAlloc (fsp + 0x128#64) ⟨0#64, 8#64, some sg₂⟩ ⟨some sess⟩ ∗
        ((fsp + 0x5c0#64) ↦₆₄ w5c0) ∗
        ((fsp + 0x5c8#64) ↦₆₄ w5c8) ∗
        memRegion (fsp + 0x1600#64) 48 ∗
        A.pool lim st s ∗ stackAt fsp (stk - cliInitiateFrame)) ∗ Rest) Q Qp oom := by
  intro fsp
  have halign_s : s.spAligned = true := spAligned_fsp hsp_align hsp
  change s.sp = fsp at hsp
  change s.readReg64 (.gpr 21#5) = fsp + 0x80#64 at hx21
  apply s5_with_rodata_oom (hRodataStoreSlot hinv.2)
  generalize hshim : lsmpl.base 605 = shimAddr
  conv => arg 4; simp only [sepConj_assoc]
  s5_have_eq hpStep1 :
      (((lsρ cliSessionVtSym + 32#64) ↦₆₄ᵣ shimAddr) ∗
        ((fsp + 0xd0#64) ↦₆₄ x.peerA) ∗
        ((fsp + 0xe0#64) ↦₆₄ (x.stores + 0xf0#64)) ∗
        ((fsp + 0xe8#64) ↦₆₄ lsρ cliSessionVtSym)) ∗ ?remStep1 := by
    s5_ac_rfl
  rw [initEntryPlaced_eq_blkPl] at hpc
  apply sepWPp_step_to_lscro_vm_mem_framed hinv hpStep1 (mid := shimAddr)
  · dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521, offStore] at hpc ⊢
    by_vm_steps (
      wp_steps
      apply sepWP_done_tpidr (by wp_norm_goal) (by wp_norm_lhs)
        (by simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm])
      exact ⟨state_exists_setMem _, rfl⟩)
  intro _ hvmp1 hinv1; clear hpStep1; subst hshim
  let cShim : StoreShimCall :=
    { self := x.stores + 0xf0#64, addrA := x.peerA, recA := fsp + 0x128#64 }
  let cStore : StoreSessionCall :=
    { addrA := x.peerA, addr := x.peer, recA := fsp + 0x128#64,
      g := ⟨0#64, 8#64, some sg₂⟩, record := ⟨some sess⟩ }
  conv => arg 4; simp only [sepConj_assoc]
  refine s5_call_sessStoreShim_placed (s0 := s0) (ret_pc := initEntryPlaced + offAfterStoreShim)
    hShim fsp cShim st ?stF1
    (by wp_norm_goal; try rfl) (by wp_norm_lhs)
    (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, hsp])
    (by simpa [State.spAligned, wp_norm, arm64_norm] using halign_s)
    (by dsimp only [initEntryPlaced, offAfterStoreShim]; wp_norm_goal; try rfl)
    (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, htr]) hinv1
    (by dsimp only [cShim]; wp_norm_goal)
    (by dsimp only [cShim]; wp_norm_goal)
    (by dsimp only [cShim]; simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, hx21])
    hFitShim ?stPre1 ?_
  case stPre1 =>
    rw [A.pool_of_vmPreserved hvmp1]
    s5_close_frame
  intro sm1 evsShim hboxShim hpc1 hrun1 hsp1 hal1 hcs1 hinv1 htr1 hfs1 hx1_1 hnz1 hal8_1
  have hx1_1_gpr : sm1.readReg64 (.gpr 1#5) = lsρ sessStoreFutVtSym := hx1_1
  conv => arg 4; dsimp only [cShim]; simp only [sepConj_assoc]
  simp (config := { zetaDelta := false }) only [CalleeSavedPreserved, wp_norm, arm64_norm] at hcs1
  rcases hcs1 with ⟨hx19_1, _, _, _, _, _, _, _, _, _, _, hvregs_1⟩
  apply s5_with_rodata_oom (sessStoreFut_poll_rodata_placed hinv1)
  generalize hpoll : lsmpl.base 570 = pollAddr
  conv => arg 4; simp only [sepConj_assoc]
  s5_have_eq hpStep2 :
      (((lsρ sessStoreFutVtSym + 24#64) ↦₆₄ᵣ pollAddr) ∗
        ((fsp + 0x5c0#64) ↦₆₄ w5c0) ∗
        ((fsp + 0x5c8#64) ↦₆₄ w5c8)) ∗ ?remStep2 := by
    s5_ac_rfl
  rw [initEntryPlaced_eq_blkPl] at hpc1
  apply sepWPp_step_to_lscro_vm_mem_framed hinv1 hpStep2 (mid := pollAddr)
  · dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521, offAfterStoreShim] at hpc1 ⊢
    by_vm_steps (
      wp_steps
      apply sepWP_done_tpidr
        (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, hx1_1])
        (by wp_norm_lhs)
        (by simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm])
      exact ⟨state_exists_setMem _, rfl⟩)
  intro _ hvmp2 hinv2; clear hpStep2; subst hpoll
  let gPoll : SessStorePollGhost :=
    { call := { call := cStore, fut := sm1.readReg64 .x0, out := fsp + 0x1600#64 },
      self := x.stores + 0xf0#64, dir := StoresGhost.opened.sessions }
  conv => arg 4; simp only [sepConj_assoc]
  refine s5_call_sessStorePoll_placed (s0 := s0) (ret_pc := initEntryPlaced + offAfterStorePoll)
    hPoll fsp gPoll (M.stepEvents evsShim st) ?stF2
    (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, hx1_1]) (by wp_norm_lhs)
    (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, hsp1])
    (by simpa [State.spAligned, wp_norm, arm64_norm] using hal1)
    (by dsimp only [initEntryPlaced, offAfterStorePoll]; wp_norm_goal; try rfl)
    (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, htr1]) hinv2
    (by dsimp only [gPoll, cStore]; wp_norm_goal)
    (by dsimp only [gPoll, cStore]; simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, hsp1])
    hnameLt hencLt opened_sessions_changed_lt
    (hFitPoll (sm1.readReg64 .x0) evsShim hboxShim)
    ?stPre2 ?_
  case stPre2 =>
    rw [A.pool_of_vmPreserved hvmp2]
    dsimp only [gPoll, cStore]; s5_close_frame
  intro sm2 evsPoll hstPoll hpc2 hrun2 hsp2 hal2 hcs2 hinv2 htr2 hfs2
  conv => arg 4; dsimp only [gPoll, cStore]
  have hfs2' : sm2.fs.files = s.fs.files := hfs2.trans hfs1
  simp (config := { zetaDelta := false }) only [CalleeSavedPreserved, wp_norm, arm64_norm, hx19_1, hx1_1, hsp1, hvregs_1] at hcs2
  rcases hcs2 with ⟨hx19_2, _, _, _, _, _, _, _, _, _, _, hvregs_2⟩
  refine sepWPp_weaken_pre ?_
    (hnext sm2 (sm1.readReg64 .x0) evsShim evsPoll ?junkRO1 hboxShim hstPoll
      hpc2 hrun2 hsp2 hvregs_2 hinv2 htr2 hfs2' hx19_2)
  conv => lhs; simp (config := { zetaDelta := false, failIfUnchanged := false }) only [BitVec.add_zero, hsp, hsp1, hx1_1_gpr]
  exact Entails.of_eq (by dsimp only [Reg.x0, fsp]; s5_ac_rfl)

private theorem stage5_store_drop_dealloc_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    [InitTraceFsSound mmpl gh W]
    {B : RunBudgets} {x : InitGhost} {fut : BitVec 64}
    {st : M.σ} {Rest : SepProp} {stk : Nat}
    {s0 s : State} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hAlloc : AllocContractsXCliPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hFutDrop : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 547)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl futDropBudgetSpec))
    (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hpc : s.pc = initEntryPlaced + offAfterStorePoll)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - BitVec.ofNat 64 cliInitiateFrame) (hsp_align : s0.spAligned = true)
    (hinv : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s.mem) (htr : s.trace = s0.trace)
    (hnext : ∀ (sm : State) (JunkRO : SepProp),
      sm.pc = initEntryPlaced + offStoreDeallocDone →
      sm.status = .Running →
      sm.sp = s0.sp - BitVec.ofNat 64 cliInitiateFrame →
      calleeSavedVRegs sm = calleeSavedVRegs s →
      LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem →
      sm.trace = s0.trace →
      sm.fs.files = s.fs.files →
      sm.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) →
      sm.readReg64 (.gpr 26#5) = 0xFFFFFFFFFFFFFFFE#64 →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sm
        ((let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
          ((fsp + 0x5c0#64) ↦₆₄ fut) ∗
          ((fsp + 0x5c8#64) ↦₆₄ lsρ sessStoreFutVtSym) ∗
          memRegion (fsp + 0x1600#64) 48 ∗
          A.pool lim (M.stepEvents (rustDeallocEvents 32 8) st) sm ∗
          stackAt fsp (stk - cliInitiateFrame)) ∗ Rest ∗ JunkRO) Q Qp oom) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s
      ((A.live fut 32 8 ∗
        sessStoreBoxAt fut (x.stores + 0xf0#64) x.peerA (fsp + 0x128#64) 1#8 ∗
        ((fsp + 0x5c0#64) ↦₆₄ fut) ∗
        ((fsp + 0x5c8#64) ↦₆₄ lsρ sessStoreFutVtSym) ∗
        ((fsp + 0x1600#64) ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗
        memRegion ((fsp + 0x1600#64) + 8#64) 40 ∗
        A.pool lim st s ∗ stackAt fsp (stk - cliInitiateFrame)) ∗ Rest) Q Qp oom := by
  intro fsp
  have hDealloc := s5_dealloc_ok_at_placed hAlloc
  have halign_s : s.spAligned = true := spAligned_fsp hsp_align hsp
  change s.sp = fsp at hsp
  conv => arg 4; simp only [sepConj_assoc]
  s5_have_eq hpTail5 : memRegion ((fsp + 0x1600#64) + 8#64) 40 ∗ ?tail5Rem := by
    s5_ac_rfl
  refine sepWPp_weaken_pre (Entails.trans (Entails.of_eq hpTail5)
    (sepConj_mono_left (tail40_words5 (fsp + 0x1600#64)))) ?_
  conv => arg 4; simp only [sepExists_sepConj_left, sepConj_assoc]
  apply sepWPp_exists_left; intro tw1; apply sepWPp_exists_left; intro tw2
  apply sepWPp_exists_left; intro tw3; apply sepWPp_exists_left; intro tw4
  apply sepWPp_exists_left; intro tw5
  have hsretOffs := sret_word_offs fsp
  conv => arg 4; rw [hsretOffs.1, hsretOffs.2.1, hsretOffs.2.2.1, hsretOffs.2.2.2.1, hsretOffs.2.2.2.2]
  apply s5_with_rodata_oom (sessStoreFut_drop_rodata_placed hinv)
  generalize hdrop : lsmpl.base 547 = dropAddr
  s5_have_eq hpStep3 :
      (((lsρ sessStoreFutVtSym) ↦₆₄ᵣ dropAddr) ∗ ((fsp + 0x1600#64) ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗
        ((fsp + 5640#64) ↦₆₄ tw1) ∗ ((fsp + 5648#64) ↦₆₄ tw2) ∗ ((fsp + 5656#64) ↦₆₄ tw3) ∗
        ((fsp + 5664#64) ↦₆₄ tw4) ∗ ((fsp + 5672#64) ↦₆₄ tw5) ∗
        ((fsp + 1480#64) ↦₆₄ lsρ sessStoreFutVtSym) ∗
        ((fsp + 1472#64) ↦₆₄ fut)) ∗
      (A.live fut 32 8 ∗
        sessStoreBoxAt fut (x.stores + 0xf0#64) x.peerA (fsp + 0x128#64) 1#8 ∗
        A.pool lim st s ∗ stackAt fsp (stk - cliInitiateFrame) ∗ Rest) := by s5_ac_rfl
  suffices hAfterDrop : ∀ (sm3 : State) (dAddr : BitVec 64) {P3 : SepProp},
      P3 = (((lsρ sessStoreFutVtSym) ↦₆₄ᵣ dAddr) ∗ ((fsp + 0x1600#64) ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗
        ((fsp + 5640#64) ↦₆₄ tw1) ∗ ((fsp + 5648#64) ↦₆₄ tw2) ∗ ((fsp + 5656#64) ↦₆₄ tw3) ∗
        ((fsp + 5664#64) ↦₆₄ tw4) ∗ ((fsp + 5672#64) ↦₆₄ tw5) ∗
        ((fsp + 1480#64) ↦₆₄ lsρ sessStoreFutVtSym) ∗
        ((fsp + 1472#64) ↦₆₄ fut)) ∗
      (A.live fut 32 8 ∗
        sessStoreBoxAt fut (x.stores + 0xf0#64) x.peerA (fsp + 0x128#64) 1#8 ∗
        A.pool lim st sm3 ∗ stackAt fsp (stk - cliInitiateFrame) ∗ Rest) →
      sm3.pc = initEntryPlaced + offStoreDealloc →
      sm3.status = .Running →
      sm3.sp = fsp →
      sm3.spAligned = true →
      sm3.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) →
      sm3.readReg64 (.gpr 22#5) = lsρ sessStoreFutVtSym →
      sm3.readReg64 (.gpr 23#5) = fut →
      sm3.readReg64 (.gpr 26#5) = 0xFFFFFFFFFFFFFFFE#64 →
      calleeSavedVRegs sm3 = calleeSavedVRegs s →
      LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl sm3.mem →
      sm3.trace = s0.trace →
      sm3.fs.files = s.fs.files →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sm3 P3 Q Qp oom by
    rw [initEntryPlaced_eq_blkPl] at hpc
    by_cases hdropNe : dropAddr = 0#64
    · apply sepWPp_step_to_lscro_vm_mem_framed hinv hpStep3 (mid := initEntryPlaced + offStoreDealloc)
      · dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521, offAfterStorePoll, offStoreDealloc] at hpc ⊢
        rw [initEntryPlaced_eq_blkPl]
        by_vm_steps (
          wp_steps
          simp (config := { failIfUnchanged := false }) only [
            hdropNe, beq_self_eq_true, ↓reduceIte]
          try wp_steps
          apply sepWP_done_tpidr (by wp_norm_goal) (by wp_norm_lhs)
            (by simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm])
          exact ⟨state_exists_setMem _, rfl⟩)
      intro _ hvmp3 hinv3; clear hpStep3
      refine sepWPp_weaken_pre (by rw [← A.pool_of_vmPreserved hvmp3]; exact Entails.refl _) ?_
      exact hAfterDrop _ 0#64 rfl
        (by dsimp only [initEntryPlaced, offStoreDealloc]; wp_norm_goal; try rfl)
        (by wp_norm_lhs)
        (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, hsp])
        (by simpa [State.spAligned, wp_norm, arm64_norm, hsp] using halign_s)
        (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal)
        (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [calleeSavedVRegs, wp_norm, arm64_norm])
        hinv3
        (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, htr])
        (by wp_norm_goal)
    · apply sepWPp_step_to_lscro_vm_mem_framed hinv hpStep3 (mid := dropAddr)
      · dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521, offAfterStorePoll] at hpc ⊢
        by_vm_steps (
          wp_steps
          simp (config := { failIfUnchanged := false }) only [
            beq_eq_false_iff_ne.mpr hdropNe, Bool.false_eq_true, ↓reduceIte]
          try wp_steps
          apply sepWP_done_tpidr (by wp_norm_goal) (by wp_norm_lhs)
            (by simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm])
          exact ⟨state_exists_setMem _, rfl⟩)
      intro _ hvmp3 hinv3; clear hpStep3; subst hdrop
      refine s5_call_futDrop_pool_placed (A := A) (lim := lim) (s0 := s0)
        (ret_pc := initEntryPlaced + offStoreDealloc)
        hFutDrop fsp st ?stF3
        (by wp_norm_goal; try rfl) (by wp_norm_lhs)
        (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, hsp])
        (by simpa [State.spAligned, wp_norm, arm64_norm] using halign_s)
        (by dsimp only [initEntryPlaced, offStoreDealloc]; wp_norm_goal; try rfl)
        (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, htr]) hinv3
        ?stPre3 ?_
      case stPre3 =>
        rw [A.pool_of_vmPreserved hvmp3]
        s5_close_frame
      intro sm3 hpc3 hrun3 hsp3 hal3 hcs3 hinv3 htr3 hfs3
      simp (config := { zetaDelta := false }) only [CalleeSavedPreserved, wp_norm, arm64_norm] at hcs3
      rcases hcs3 with ⟨hx19_3, _, _, hx22_3, hx23_3, _, _, hx26_3, _, _, _, hvregs_3⟩
      refine sepWPp_weaken_pre (Entails.of_eq (by s5_ac_rfl))
        (hAfterDrop sm3 (lsmpl.base 547) rfl hpc3 hrun3 hsp3 hal3 hx19_3 hx22_3 hx23_3 hx26_3
          hvregs_3 hinv3 htr3 hfs3)
  clear hpStep3
  intro sm3 dAddr P3 hP3Eq hpc3 hrun3 hsp3 hal3 hx19_3 hx22_3 hx23_3 hx26_3 hvregs_3 hinv3 htr3 hfs3
  subst hP3Eq
  apply s5_with_rodata_oom (sessStoreFut_size_rodata_placed hinv3)
  apply s5_with_rodata_oom (sessStoreFut_align_rodata_placed hinv3)
  conv => arg 4; simp only [sepConj_assoc]
  s5_have_eq hpStep4 :
      (((lsρ sessStoreFutVtSym + 8#64) ↦₆₄ᵣ 32#64) ∗
        ((lsρ sessStoreFutVtSym + 16#64) ↦₆₄ᵣ 8#64)) ∗ ?remStep4 := by
    s5_ac_rfl
  rw [initEntryPlaced_eq_blkPl] at hpc3
  apply sepWPp_step_to_lscro_vm_mem_framed hinv3 hpStep4 (mid := lsρ lsRustDeallocSymCli)
  · dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521, offStoreDealloc, lsρ] at hpc3 hx22_3 ⊢
    by_vm_steps (
      wp_steps
      apply sepWP_done_tpidr (by wp_norm_goal) (by wp_norm_lhs)
        (by simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm])
      exact ⟨state_exists_setMem _, rfl⟩)
  intro _ hvmp4 hinv4; clear hpStep4
  have hboxMem := sessStoreBoxAt_entails_memRegion32 fut (x.stores + 0xf0#64)
    x.peerA (fsp + 0x128#64) 1#8
  conv =>
    arg 4
    rw [s5_stackAt_sub_split fsp (extHook_le_stkSub hstk) (stkSub_hi hstk64)]
    simp only [sepConj_assoc]
  refine s5_call_dealloc_placed (s0 := s0) (ret_pc := initEntryPlaced + offStoreDeallocDone)
    hDealloc fsp fut 32 8 st ?stF4
    (by dsimp only [lsρ]; wp_norm_goal; try rfl) (by wp_norm_lhs)
    (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, hsp3])
    (by simpa [State.spAligned, wp_norm, arm64_norm] using hal3)
    (by dsimp only [initEntryPlaced, offStoreDeallocDone]; wp_norm_goal; try rfl)
    (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, htr3]) hinv4
    (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, hx23_3])
    (by wp_norm_goal) (by wp_norm_goal) ⟨layoutOk_32_8, by decide⟩
    ?stPre4 ?_
  case stPre4 =>
    rw [A.pool_of_vmPreserved hvmp4]
    s5_have_eq hpull :
        sessStoreBoxAt fut (x.stores + 0xf0#64) x.peerA (fsp + 0x128#64) 1#8 ∗
        ?restBox := by
      conv => lhs; simp (config := { zetaDelta := false, failIfUnchanged := false }) only [BitVec.add_zero, hsp3]
      s5_ac_rfl
    refine Entails.trans (Entails.of_eq hpull)
      (Entails.trans (sepConj_mono_left hboxMem) ?_)
    s5_close_frame
  intro sm4 hpc4 hrun4 hsp4 hal4 hcs4 hinv4 htr4 hfs4
  have hfs4' : sm4.fs.files = s.fs.files := hfs4.trans hfs3
  simp (config := { zetaDelta := false }) only [CalleeSavedPreserved, wp_norm, arm64_norm, hx19_3, hx26_3, hvregs_3] at hcs4
  rcases hcs4 with ⟨hx19_4, _, _, _, _, _, _, hx26_4, _, _, _, hvregs_4⟩
  s5_rw_pre (s5_stackAt_sub_split fsp (extHook_le_stkSub hstk) (stkSub_hi hstk64)).symm
  have hw48 := words6_entails_memRegion48 (fsp + 0x1600#64)
    0xFFFFFFFFFFFFFFFE#64 tw1 tw2 tw3 tw4 tw5
  refine sepWPp_weaken_pre ?_
    (hnext sm4 ?junkRO2 hpc4 hrun4 hsp4 hvregs_4 hinv4 htr4 hfs4' hx19_4 hx26_4)
  have hsretSymm := sret_word_offs_symm fsp
  s5_have_eq hp1 :
      (((fsp + 0x1600#64) ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗
        (((fsp + 0x1600#64) + 0x08#64) ↦₆₄ tw1) ∗ (((fsp + 0x1600#64) + 0x10#64) ↦₆₄ tw2) ∗
        (((fsp + 0x1600#64) + 0x18#64) ↦₆₄ tw3) ∗ (((fsp + 0x1600#64) + 0x20#64) ↦₆₄ tw4) ∗
        (((fsp + 0x1600#64) + 0x28#64) ↦₆₄ tw5)) ∗ ?remW48 := by
    conv =>
      lhs; simp (config := { zetaDelta := false, failIfUnchanged := false }) only [BitVec.add_zero, hsp, hsp3]
      rw [hsretSymm.1, hsretSymm.2.1, hsretSymm.2.2.1, hsretSymm.2.2.2.1, hsretSymm.2.2.2.2]
    s5_ac_rfl
  refine Entails.trans (Entails.of_eq hp1) (Entails.trans (sepConj_mono_left hw48) ?_)
  exact Entails.of_eq (by dsimp only [fsp]; s5_ac_rfl)

/-! ## Store and Cleanup Theorems -/

/-- Continuation from `offStoreDeallocDone` (`+0x1810`): deallocates `pqspkPtr`, drops
`sessionRecordAt` inline (`dropSessionStructure`), jumps to `offEpilogue`, and enters
`stage5_epilogue_placed_ok`. -/
theorem stage5_cleanup_after_store_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    [InitTraceFsSound mmpl gh W]
    {B : RunBudgets} {S : RunSem} {x : InitGhost}
    {st0 st : M.σ} {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)} {pqspkPtr : BitVec 64} {opkId : BitVec 32}
    {sg₂ : SessionGhost} {sess : Session (List (BitVec 8))} {b5b8 : BitVec 8}
    {Extra : SepProp} {stk : Nat} {s0 s : State}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hAlloc : AllocContractsXCliPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hDropSS : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 512)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget.dropSessionStructureLocal2Spec
          M A lim)))
    (hEnv : ∀ evsDrop, FreeOnlyEvs evsDrop →
      ∃ evs, InitEnv x evs ∧
        M.stepEvents evsDrop (M.stepEvents (rustDeallocEvents 1568 1) st) = M.stepEvents evs st0)
    (hinitOk : InitOk₀ ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val)
    (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hekLen : ekASk.length = 32 ∧ ekAPk.length = 32) (hkpkLen : x.bundle.kpk.length = 1568)
    (hans : S.initiate x.F x.peer.val x.me.val x.bundle x.coins =
      some (some (initAcceptStoresGhost x.F x.peer.val x.bundle.idKey
        (Record.encodeRecord ⟨some sess⟩), ())))
    (hpc : s.pc = initEntryPlaced + offStoreDeallocDone)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - BitVec.ofNat 64 cliInitiateFrame)
    (hsp_align : s0.spAligned = true) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hinv : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s.mem) (htr : s.trace = s0.trace)
    (hfs0 : s0.fs.files = x.F) (hfss : s.fs.files = x.F)
    (hx19 : s.readReg64 (.gpr 19#5) = x.ret) (hx26 : s.readReg64 (.gpr 26#5) = 0xFFFFFFFFFFFFFFFE#64)
    (hpost : ∀ sf Pf, InitExitPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Q sf Pf) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s
      (dirAt A.repAlloc x.stores StoresGhost.opened.identity.own ∗
        dirAt A.repAlloc (x.stores + 0x28#64)
          (StoresGhost.opened.identity.saveUpd cliIo.rd x.F x.peer.val x.bundle.idKey).peers ∗
        dirAt A.repAlloc (x.stores + 0x50#64) StoresGhost.opened.signed ∗
        dirAt A.repAlloc (x.stores + 0x78#64) StoresGhost.opened.kyber.oneTime ∗
        dirAt A.repAlloc (x.stores + 0xa0#64) StoresGhost.opened.kyber.lastResort ∗
        dirAt A.repAlloc (x.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
        dirAt A.repAlloc (x.stores + 0xf0#64)
          (StoresGhost.opened.sessions.put (addressText x.peer.val)
            (E2E.Record.encodeRecord ⟨some sess⟩)) ∗
        dirAt A.repAlloc (x.stores + 0x118#64) StoresGhost.opened.pub ∗
        protocolAddressAt A.repAlloc x.peer x.peerA ∗ protocolAddressAt A.repAlloc x.me x.meA ∗
        cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
        (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗ FromRecordCallees.lsLogOff ∗
        A.pool lim st s ∗ initSaved s0 ∗
        memRegion fsp 0xd0 ∗ initArgsAtPlaced fsp x s0 ∗
        sessionRecordAt A.repAlloc (fsp + 0x128#64) ⟨0#64, 8#64, some sg₂⟩ ⟨some sess⟩ ∗
        stage3KeySlotsAt A.repAlloc fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
        memRegion (fsp + 0x460#64) 344 ∗ ((fsp + 0x5b8#64) ↦₈ b5b8) ∗ ((fsp + 0x5b9#64) ↦₈ 0#8) ∗
        memRegion (fsp + 0x5ba#64) (initLocalsSize - 0x5ba) ∗
        stackAt fsp (stk - cliInitiateFrame) ∗ Extra) Q Qp oom := by
  intro fsp
  conv => arg 4; rw [stage3KeySlotsAt_dealloc_split_placed A]; simp only [sepConj_assoc]
  s5_have_eq hpPre :
      (sessionRecordAt A.repAlloc (fsp + 0x128#64) ⟨0#64, 8#64, some sg₂⟩ ⟨some sess⟩ ∗
        ((fsp + 0x428#64) ↦₆₄ pqspkPtr) ∗ ((fsp + 0x430#64) ↦₆₄ 1568#64) ∗
        A.live pqspkPtr 1568 1 ∗ (pqspkPtr ↦ₛ x.bundle.kpk) ∗
        ((fsp + 0x5b9#64) ↦₈ 0#8) ∗ A.pool lim st s ∗
        stackAt fsp (stk - cliInitiateFrame)) ∗ ?remClean := by
    s5_ac_rfl
  refine sepWPp_weaken_pre (Entails.of_eq hpPre)
    (stage5_dealloc_and_drop_rec_placed_ok hAlloc hDropSS hstk hstk64 hkpkLen
      hpc hrun hsp hsp_align hinv htr hx26 ?_)
  intro sm evsDrop hfreeDrop hpcE hrunE hspE hvregsE hinvE htrE hfsE hx19E hx26E
  obtain ⟨evs, hInitEnv, hevsEq⟩ := hEnv evsDrop hfreeDrop
  have hloc := collapse_initLocals_from_rest_placed fsp (x := x) (kp := kp)
    (ekASk := ekASk) (ekAPk := ekAPk) (pqspkPtr := pqspkPtr) (opkId := opkId) (s0 := s0)
    0#64 8#64 0#64 b5b8 0#8 hekLen
  let gAcc := initAcceptStoresGhost x.F x.peer.val x.bundle.idKey
    (Record.encodeRecord ⟨some sess⟩)
  refine sepWPp_weaken_pre ?_
    (stage5_epilogue_placed_ok (B := B) hInitEnv gAcc (.ok ()) emp Extra
      hstk hstk64 hpcE hrunE hspE hsp_align
      (hvregsE.trans hvregs) (hx19E.trans hx19) htrE
      hfs0 (hfsE.trans hfss)
      (fun _ => slotOut_ok_of_accept hinitOk hans)
      (by
        simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, hx26E]
        exact words6_ok_entails_initResAt A.repAlloc x.ret _ _ _ _ _)
      hpost
      hevsEq)
  s5_have_eq hpLoc :
      (memRegion fsp 0xd0 ∗ initArgsAtPlaced fsp x s0 ∗
        ((fsp + 0x128#64) ↦₆₄ 0#64) ∗ ((fsp + 0x130#64) ↦₆₄ 8#64) ∗ ((fsp + 0x138#64) ↦₆₄ 0#64) ∗
        memRegion (fsp + 0x140#64) 344 ∗
        ((fsp + 0x428#64) ↦₆₄ pqspkPtr) ∗ ((fsp + 0x430#64) ↦₆₄ 1568#64) ∗
        stage3KeySlotsRestPlaced fsp x.bundle kp ekASk ekAPk opkId ∗
        memRegion (fsp + 0x460#64) 344 ∗
        ((fsp + 0x5b8#64) ↦₈ b5b8) ∗ ((fsp + 0x5b9#64) ↦₈ 0#8) ∗
        memRegion (fsp + 0x5ba#64) (initLocalsSize - 0x5ba)) ∗ ?remEpi := by
    dsimp only [fsp] at *; s5_ac_rfl
  refine Entails.trans (Entails.of_eq hpLoc) (Entails.trans (sepConj_mono_left hloc) ?_)
  dsimp only [storesAt, gAcc, initAcceptStoresGhost]
  rw [saveUpd_own_eq_placed]
  simp only [emp_sepConj, sepConj_emp]
  exact Entails.of_eq (by dsimp only [fsp]; s5_ac_rfl)

/-- Continuation from `offStore` (`+0x1768`): calls `store_session` shim + poll + future drop +
box dealloc, merges scratch stack, and hands off to `stage5_cleanup_after_store_placed_ok`. -/
theorem stage5_store_and_cleanup_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {StoreEnv : SessStorePollGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    [InitTraceFsSound mmpl gh W]
    {B : RunBudgets} {S : RunSem} {x : InitGhost}
    {st0 st : M.σ} {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)} {pqspkPtr : BitVec 64} {opkId : BitVec 32}
    {sg₂ : SessionGhost} {sess : Session (List (BitVec 8))}
    {w5c0 w5c8 w5d0 : BitVec 64} {b5b8 : BitVec 8} {Extra : SepProp} {stk : Nat}
    {s0 s : State} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hAlloc : AllocContractsXCliPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRodataStoreSlot : ∀ {m : Memory} {P : SepProp},
      LibsignalRoLoaded lsmpl m → (m ⊨ P) →
        (m ⊨ ((lsρ cliSessionVtSym + 32#64) ↦₆₄ᵣ lsmpl.base 605) ∗ P))
    (hShim : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 605)
      (sessStoreShimSpecPlaced A lim (stk - cliInitiateFrame)))
    (hPoll : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 570)
      (sessStorePollSpecPlaced A lim StoreEnv (stk - cliInitiateFrame)))
    (hFutDrop : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 547)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl futDropBudgetSpec))
    (hDropSS : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 512)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget.dropSessionStructureLocal2Spec
          M A lim)))
    (hFitShim : FitsEnv M lim st (BoxAllocEnv 32))
    (hFitPoll : ∀ (fut : BitVec 64) (evsShim : List AllocEvent),
      BoxAllocEnv 32 evsShim →
      FitsEnv M lim (M.stepEvents evsShim st)
        (StoreEnv
          { call :=
              { call :=
                  { addrA := x.peerA
                    addr := x.peer
                    recA := s0.sp - BitVec.ofNat 64 cliInitiateFrame + 0x128#64
                    g := ⟨0#64, 8#64, some sg₂⟩
                    record := ⟨some sess⟩ }
                fut := fut
                out := s0.sp - BitVec.ofNat 64 cliInitiateFrame + 0x1600#64 }
            self := x.stores + 0xf0#64
            dir := StoresGhost.opened.sessions }))
    (hEnv : ∀ (fut : BitVec 64) (evsShim evsPoll evsDrop : List AllocEvent),
      BoxAllocEnv 32 evsShim →
      StoreEnv
        { call :=
            { call :=
                { addrA := x.peerA
                  addr := x.peer
                  recA := s0.sp - BitVec.ofNat 64 cliInitiateFrame + 0x128#64
                  g := ⟨0#64, 8#64, some sg₂⟩
                  record := ⟨some sess⟩ }
              fut := fut
              out := s0.sp - BitVec.ofNat 64 cliInitiateFrame + 0x1600#64 }
          self := x.stores + 0xf0#64
          dir := StoresGhost.opened.sessions } evsPoll →
      FreeOnlyEvs evsDrop →
      ∃ evs, InitEnv x evs ∧
        M.stepEvents evsDrop
          (M.stepEvents (rustDeallocEvents 1568 1)
            (M.stepEvents (rustDeallocEvents 32 8)
              (M.stepEvents evsPoll (M.stepEvents evsShim st)))) = M.stepEvents evs st0)
    (hinitOk : InitOk₀ ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val)
    (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hekLen : ekASk.length = 32 ∧ ekAPk.length = 32) (hkpkLen : x.bundle.kpk.length = 1568)
    (hencLt : (Record.encodeRecord ⟨some sess⟩).length < 2 ^ 32)
    (hans : S.initiate x.F x.peer.val x.me.val x.bundle x.coins =
      some (some (initAcceptStoresGhost x.F x.peer.val x.bundle.idKey
        (Record.encodeRecord ⟨some sess⟩), ())))
    (hpc : s.pc = initEntryPlaced + offStore) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - BitVec.ofNat 64 cliInitiateFrame) (hsp_align : s0.spAligned = true)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hinv : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace) (hfs0 : s0.fs.files = x.F) (hfss : s.fs.files = x.F)
    (hx19 : s.readReg64 (.gpr 19#5) = x.ret)
    (hx21 : s.readReg64 (.gpr 21#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x80#64)
    (hpost : ∀ sf Pf, InitExitPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Q sf Pf) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s
      (dirAt A.repAlloc x.stores StoresGhost.opened.identity.own ∗
        dirAt A.repAlloc (x.stores + 0x28#64)
          (StoresGhost.opened.identity.saveUpd cliIo.rd x.F x.peer.val x.bundle.idKey).peers ∗
        dirAt A.repAlloc (x.stores + 0x50#64) StoresGhost.opened.signed ∗
        dirAt A.repAlloc (x.stores + 0x78#64) StoresGhost.opened.kyber.oneTime ∗
        dirAt A.repAlloc (x.stores + 0xa0#64) StoresGhost.opened.kyber.lastResort ∗
        dirAt A.repAlloc (x.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
        dirAt A.repAlloc (x.stores + 0xf0#64) StoresGhost.opened.sessions ∗
        dirAt A.repAlloc (x.stores + 0x118#64) StoresGhost.opened.pub ∗
        protocolAddressAt A.repAlloc x.peer x.peerA ∗ protocolAddressAt A.repAlloc x.me x.meA ∗
        cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
        (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗
        FromRecordCallees.lsLogOff ∗ A.pool lim st s ∗ initSaved s0 ∗
        memRegion fsp 0xd0 ∗
        initArgsAtPlaced fsp x s0 ∗
        sessionRecordAt A.repAlloc (fsp + 0x128#64) ⟨0#64, 8#64, some sg₂⟩ ⟨some sess⟩ ∗
        stage3KeySlotsAt A.repAlloc fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
        memRegion (fsp + 0x460#64) 344 ∗
        ((fsp + 0x5b8#64) ↦₈ b5b8) ∗ ((fsp + 0x5b9#64) ↦₈ 0#8) ∗
        stage5ScratchAt fsp w5c0 w5c8 w5d0 ∗
        stackAt fsp (stk - cliInitiateFrame) ∗ Extra)
      Q Qp oom := by
  intro fsp
  conv =>
    arg 4
    rw [initArgsAtPlaced_store_split, stage5ScratchAt_store_split_placed]
    simp only [sepConj_assoc]
  s5_have_eq hpPre1 :
      (((fsp + 0xd0#64) ↦₆₄ x.peerA) ∗
        ((fsp + 0xe0#64) ↦₆₄ (x.stores + 0xf0#64)) ∗
        ((fsp + 0xe8#64) ↦₆₄ lsρ cliSessionVtSym) ∗
        dirAt A.repAlloc (x.stores + 0xf0#64) StoresGhost.opened.sessions ∗
        protocolAddressAt A.repAlloc x.peer x.peerA ∗
        sessionRecordAt A.repAlloc (fsp + 0x128#64) ⟨0#64, 8#64, some sg₂⟩ ⟨some sess⟩ ∗
        ((fsp + 0x5c0#64) ↦₆₄ w5c0) ∗
        ((fsp + 0x5c8#64) ↦₆₄ w5c8) ∗
        memRegion (fsp + 0x1600#64) 48 ∗
        A.pool lim st s ∗ stackAt fsp (stk - cliInitiateFrame)) ∗ ?remSt1 := by
    s5_ac_rfl
  refine sepWPp_weaken_pre (Entails.of_eq hpPre1)
    (stage5_store_shim_poll_placed_ok hRodataStoreSlot hShim hPoll hFitShim hFitPoll
      hinitOk.nameLt hencLt hpc hrun hsp hsp_align hinv htr hx21 ?_)
  intro sm2 fut evsShim evsPoll JunkRO1 hboxShim hstPoll hpc2 hrun2 hsp2 hvregs2 hinv2 htr2 hfs2 hx19_2
  conv => arg 4; dsimp only; simp only [sepConj_assoc]
  s5_have_eq hpPre2 :
      (A.live fut 32 8 ∗
        sessStoreBoxAt fut (x.stores + 0xf0#64) x.peerA (fsp + 0x128#64) 1#8 ∗
        ((fsp + 0x5c0#64) ↦₆₄ fut) ∗
        ((fsp + 0x5c8#64) ↦₆₄ lsρ sessStoreFutVtSym) ∗
        ((fsp + 0x1600#64) ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗
        memRegion ((fsp + 0x1600#64) + 8#64) 40 ∗
        A.pool lim (M.stepEvents evsPoll (M.stepEvents evsShim st)) sm2 ∗
        stackAt fsp (stk - cliInitiateFrame)) ∗ ?remSt2 := by
    dsimp only [fsp] at *; s5_ac_rfl
  refine sepWPp_weaken_pre (Entails.of_eq hpPre2)
    (stage5_store_drop_dealloc_placed_ok hAlloc hFutDrop hstk hstk64
      hpc2 hrun2 hsp2 hsp_align hinv2 htr2 ?_)
  intro sm4 JunkRO2 hpc4 hrun4 hsp4 hvregs4 hinv4 htr4 hfs4 hx19_4 hx26_4
  have hscr :
      (((fsp + 0x5c0#64) ↦₆₄ fut) ∗
        ((fsp + 0x5c8#64) ↦₆₄ lsρ sessStoreFutVtSym) ∗
        memRegion (fsp + 0x1600#64) 48) ∗ stage5ScratchRestPlaced fsp w5d0 ⊢
        memRegion (fsp + 0x5ba#64) (initLocalsSize - 0x5ba) := by
    rw [← stage5ScratchAt_store_split_placed]
    exact scratch_merge fsp fut (lsρ sessStoreFutVtSym) w5d0
  refine sepWPp_weaken_pre ?_
    (stage5_cleanup_after_store_placed_ok (B := B) (kp := kp) (pqspkPtr := pqspkPtr) (opkId := opkId)
      (sg₂ := sg₂) (sess := sess) (b5b8 := b5b8) (Extra := Extra ∗ JunkRO1 ∗ JunkRO2)
      hAlloc hDropSS (fun evsDrop hfree => hEnv fut evsShim evsPoll evsDrop hboxShim hstPoll hfree)
      hinitOk hstk hstk64 hekLen hkpkLen hans
      hpc4 hrun4 hsp4 hsp_align (hvregs4.trans (hvregs2.trans hvregs)) hinv4 htr4
      hfs0 (hfs4.trans (hfs2.trans hfss)) (hx19_4.trans (hx19_2.trans hx19)) hx26_4 hpost)
  conv => arg 1; dsimp only; simp only [sepConj_assoc]
  s5_have_eq hpScr :
      ((((fsp + 0x5c0#64) ↦₆₄ fut) ∗
        ((fsp + 0x5c8#64) ↦₆₄ lsρ sessStoreFutVtSym) ∗
        memRegion (fsp + 0x1600#64) 48) ∗ stage5ScratchRestPlaced fsp w5d0) ∗ ?remScr := by
    dsimp only [fsp] at *; s5_ac_rfl
  refine Entails.trans (Entails.of_eq hpScr) (Entails.trans (sepConj_mono_left hscr) ?_)
  s5_have_eq hpArgs :
      ((((fsp + 0xd0#64) ↦₆₄ x.peerA) ∗
        ((fsp + 0xe0#64) ↦₆₄ (x.stores + 0xf0#64)) ∗
        ((fsp + 0xe8#64) ↦₆₄ lsρ cliSessionVtSym)) ∗ initArgsStoreRestPlaced fsp x s0) ∗ ?remArgs := by
    dsimp only [fsp] at *; s5_ac_rfl
  rw [← initArgsAtPlaced_store_split] at hpArgs
  refine Entails.trans (Entails.of_eq hpArgs) ?_
  exact Entails.of_eq (by dsimp only [fsp]; s5_ac_rfl)

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.AcceptTailStorePlacedBudget

end
