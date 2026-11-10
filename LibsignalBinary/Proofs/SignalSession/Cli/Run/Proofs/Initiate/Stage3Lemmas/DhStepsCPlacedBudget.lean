/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.DhStepsCPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.DhHelpersPlacedBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Budget-Threaded Stage 3 PQXDH Step C (`[LibsignalPlacement]`, `+0x0a70 → +0x0b6c`: Optional `DH4`)

Advances `+0x0a70 → +0x0b6c` across optional `DH4 = X25519(ekASk, opkPk)` under
`RustCliAllocBudget M`, unifying the `opk = none` jump (`[]`), zero-DH unwind
(`unwind1548Events`), and `opk = some` shared-secret copy (`dh4OptEvents (some dh4)`).
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false
set_option linter.dupNamespace false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option maxRecDepth 200000

open scoped CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchet
open CryptoGames.LibsignalSession (PublicKey)
open CryptoVerification (LibsignalPlacement lsmpl lsρ)
open CryptoVerification.CliHandshake.InitiatePlaced (blkPl_521 lsProg_521)
open CryptoVerification.E2E (PreKeyBundleFields UnreachedPqxdhPrimitives initiateInput modelPrims toU8)
open CryptoVerification.E2E.Pqxdh.Initiator (F_X25519 bytesToBv8)
open CryptoVerification.E2E.Pqxdh.ResponderCore (and_ff32_hi56_3 and_ff_hi56_3 bytesToBv8_length extractLsb_hi56_3 ofSignalPqxdhPrimitives zext64_trunc32_hi56_3_and_ff)
open CryptoVerification.LibsignalPublicApi.StoreKit (withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet (extHookStack memcpyName)
open CryptoVerification.LibsignalTripleRatchetRepr (speWord)
open CryptoVerification.RecordCodecs (IdentityKeyPair)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced lsRustDeallocSymCli)
open CryptoVerification.SignalSession.Cli.RunCompose (BundleV InitGhost RunSem)
open CryptoVerification.SignalSession.Cli.RunProofs (cliInitiateFrame cliInitiateNeed initDef padCoins)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate (AtStage3Placed InInitiatePlaced coinsCursorAtPlaced initProgPlaced stage3KeySlotsAt)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage3Lemmas (append_bv8_at bundleEOf_props bytesToBv8_toU8_eq cells3_to_memRegion24 dh4_none_opt dh4_some_eq dhLenWord dhPrefix dhRemAt initDef_some_none_of_dh_bad lay32 memRegion_merge_at modelPrims_x25519_len pointsToBytes_entails_memRegion_len sepWPp_conseq_oom sep_replace toU8_length_eq)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.DhStepsCPlacedBudget

noncomputable section

open Arm64 Arm64.Obj Arm64.Process ProofLib SepProp
open CryptoVerification.LibsignalSpqrV1 (Params)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEvents RustCliAllocBudget VmPreserved rustAllocEvents
   rustDeallocEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.DefsPlacedBudget
  (InitExitPostPlaced InitPanicPostPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlacedBudget
  (RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.LocalCalleesPlacedBudget
  (InitLocalCalleesPlaced calculateAgreement_cli_placed_ok pqxdhCalculateAgreementPlacedInnerSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.CollapsePlacedBudget
  (s3_block_in_vm_placed s3_block_to_call_vm_placed s3_dealloc_stack_placed s3_done_call_vm
   s3_done_in_vm)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.DefsPlacedBudget
  (s3_memcpy_pool_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.DhHelpersPlacedBudget
  (S3InvPrefixPlaced fitsEvents_s3CalcAgreeEvents_of_alloc32 s3CalcAgreeEvents s3_calc_agree_of_ok
   s3_dh_unwind_1544_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.EarlyExitPlacedBudget
  (stepEvents_unwind1548Events unwind1548Events)
open Arm64.Obj (MultiPlacement)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate (initProgExtPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (CliGhostHooks cliGhostExterns)

attribute [local irreducible] Program.fetch Program.externAt? S3InvPrefixPlaced coinsCursorAtPlaced
attribute [local simp, local arm64_norm, local wp_norm]
  extractLsb_hi56_3 and_ff_hi56_3 and_ff32_hi56_3 zext64_trunc32_hi56_3_and_ff

/-- Allocator events along the non-unwind optional `DH4` path (`+0x0a70 → +0x0b6c`). -/
def dh4OptEvents : Option SignalPqxdh.Bytes → List AllocEvent
  | none => []
  | some _ => rustAllocEvents 32 1 ++ rustDeallocEvents 32 1

def dh4StepOkEvents : Option (BitVec 32 × PublicKey) → List AllocEvent
  | none => []
  | some _ => rustAllocEvents 32 1 ++ rustDeallocEvents 32 1

def s3Dh4CalcAgreeEvents (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (ekASk : List (BitVec 8)) : Option (BitVec 32 × PublicKey) → List AllocEvent
  | none => []
  | some (_, ok) => s3CalcAgreeEvents X W (toU8 ekASk) (toU8 ok.bytes.toList)

theorem stepEvents_dh4OptEvents_none (M : AllocCostModel) (st : M.σ) :
    st = M.stepEvents (dh4OptEvents none) st :=
  (M.stepEvents_nil st).symm

theorem stepEvents_dh4OptEvents_some (M : AllocCostModel) (d : SignalPqxdh.Bytes) (st : M.σ) :
    M.stepEvents (rustDeallocEvents 32 1) (M.stepEvents (rustAllocEvents 32 1) st) =
      M.stepEvents (dh4OptEvents (some d)) st :=
  (M.stepEvents_append (rustAllocEvents 32 1) (rustDeallocEvents 32 1) st).symm

theorem fitsEvents_s3Dh4CalcAgreeEvents {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {X : UnreachedPqxdhPrimitives} {W : CliHooks} {ekASk : List (BitVec 8)}
    {opk : Option (BitVec 32 × PublicKey)}
    (hFit : opk.isSome = true → FitsEvents M lim st (rustAllocEvents 32 1)) :
    FitsEvents M lim st (s3Dh4CalcAgreeEvents X W ekASk opk) := by
  rcases opk with _ | ⟨_, ok⟩
  · trivial
  · exact fitsEvents_s3CalcAgreeEvents_of_alloc32 (hFit rfl)

theorem fitsEvents_s3Dh4CalcAgreeEvents_of_alloc32 {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {X : UnreachedPqxdhPrimitives} {W : CliHooks} {ekASk : List (BitVec 8)}
    {opk : Option (BitVec 32 × PublicKey)}
    (hFit : FitsEvents M lim st (rustAllocEvents 32 1)) :
    FitsEvents M lim st (s3Dh4CalcAgreeEvents X W ekASk opk) :=
  fitsEvents_s3Dh4CalcAgreeEvents fun _ => hFit

private theorem sec128_re_placed (secretsPtr : BitVec 64) (bs : SignalPqxdh.Bytes)
    (h128 : (bytesToBv8 bs).length = 128) :
    (secretsPtr ↦ₛ bytesToBv8 bs) ∗ memRegion (secretsPtr + 128#64) 32 ∗
      memRegion (secretsPtr + 160#64) 32 ⊢ memRegion secretsPtr 192 := by
  refine Entails.trans (sepConj_mono_left (pointsToBytes_entails_memRegion_len h128)) ?_
  rw [memRegion_merge_at (secretsPtr + 128#64) 32 32 (secretsPtr + 160#64) (by clear * -; bv_omega) (by decide),
      memRegion_merge_at secretsPtr 128 64 (secretsPtr + 128#64) (by clear * -; bv_omega) (by decide)]
  exact Entails.refl _

private theorem s3_repack4_placed (A : RustAlloc) (fsp : BitVec 64) (b : BundleV)
    (kp : IdentityKeyPair) (ekASk ekAPk : List (BitVec 8)) (pqspkPtr : BitVec 64)
    (opkId oid : BitVec 32) (ok : PublicKey) (hopk : b.opk = some (oid, ok)) :
    ((fsp + 0x439#64) ↦ₛ ok.bytes.toList) ∗
      (((fsp + 0x298#64) ↦ₛ ekAPk) ∗ memRegion (fsp + 0x2b8#64) 0x48 ∗
       ((fsp + 0x300#64) ↦₃₂ 1#32) ∗ ((fsp + 0x304#64) ↦₃₂ opkId) ∗
       memRegion (fsp + 0x308#64) 0x40 ∗
       ((fsp + 0x348#64) ↦ₛ kp.identityKey.publicKey.bytes.toList) ∗
       ((fsp + 0x368#64) ↦ₛ kp.privateKey.bytes.toList) ∗
       ((fsp + 0x388#64) ↦ₛ ekAPk) ∗ ((fsp + 0x3a8#64) ↦ₛ ekASk) ∗
       ((fsp + 0x3c8#64) ↦ₛ b.idKey.publicKey.bytes.toList) ∗
       ((fsp + 0x3e8#64) ↦ₛ b.spk.bytes.toList) ∗
       ((fsp + 0x408#64) ↦ₛ b.spk.bytes.toList) ∗
       ((fsp + 0x428#64) ↦₆₄ pqspkPtr) ∗ ((fsp + 0x430#64) ↦₆₄ 1568#64) ∗
       A.live pqspkPtr 1568 1 ∗ (pqspkPtr ↦ₛ b.kpk) ∗
       ((fsp + 0x438#64) ↦₈ 1#8) ∗
       ((fsp + 0x459#64) ↦₈ 0#8) ∗ memRegion (fsp + 0x45a#64) 6) =
    stage3KeySlotsAt A fsp b kp ekASk ekAPk pqspkPtr opkId := by
  dsimp only [stage3KeySlotsAt]
  simp only [hopk, Option.isSome_some, ↓reduceIte,
    show (1#32 : BitVec 32).truncate 8 = 1#8 from rfl]
  sep_ac_rfl

set_option maxHeartbeats 1600000 in
/-- Budget-threaded optional `DH4` step (`+0x0a70 → +0x0b6c`) from a Block `207` witness. -/
theorem dh4_step_of_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {st0 st : M.σ} {be : PreKeyBundleFields} {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)} {pqspkPtr secretsPtr : BitVec 64} {opkId : BitVec 32}
    {dh1 dh2 dh3 : SignalPqxdh.Bytes} {stk : Nat} {s0 s3 s : State}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hCalc : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 207)
      (withLsCodeRoLoaded lsmpl
        (pqxdhCalculateAgreementPlacedInnerSpec (modelPrims X ⟨W.C, W.Q⟩) A lim)))
    (hFit : FitsEvents M lim st (s3Dh4CalcAgreeEvents X W ekASk x.bundle.opk))
    (hEnv :
      let P := modelPrims X ⟨W.C, W.Q⟩
      let inp := initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)
      SignalPqxdh.dhOptNonZero (inp.bundle.opkB?.map fun (_, opkPk) => P.x25519 inp.ekASk opkPk) =
        false →
      ∃ evs, InitEnv x evs ∧
        M.stepEvents (rustDeallocEvents 1568 1) (M.stepEvents (rustDeallocEvents 192 1) st) =
          M.stepEvents evs st0)
    (hS : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hs3 : AtStage3Placed W X x be kp ekASk ekAPk pqspkPtr opkId s0 s3)
    (hpost : ∀ sf Pf, InitExitPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Q sf Pf)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf)
    (hdh1_len32 : dh1.length = 32) (hdh2_len32 : dh2.length = 32) (hdh3_len32 : dh3.length = 32)
    (hsecNonNull : secretsPtr ≠ 0#64)
    (hctrl : InInitiatePlaced s0 s 0xa70) (htr : s.trace = s0.trace)
    (hx20 : s.readReg64 (.gpr 20#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x348#64)
    (hx21 : s.readReg64 (.gpr 21#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x388#64)
    (hx22 : s.readReg64 (.gpr 22#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x408#64)
    (hx26 : s.readReg64 (.gpr 26#5) = 128#64)
    (hnext : ∀ (sb : State) (dh4? : Option SignalPqxdh.Bytes),
      let P := modelPrims X ⟨W.C, W.Q⟩
      let inp := initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)
      let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
      dh4? = (inp.bundle.opkB?.map fun (_, opkPk) => P.x25519 inp.ekASk opkPk) →
      SignalPqxdh.dhOptNonZero dh4? = true →
      (∀ d, dh4? = some d → d.length = 32) →
      InInitiatePlaced s0 sb 0xb6c → sb.trace = s0.trace →
      sb.readReg64 (.gpr 20#5) = fsp + 0x348#64 → sb.readReg64 (.gpr 21#5) = fsp + 0x388#64 →
      sb.readReg64 (.gpr 22#5) = fsp + 0x408#64 →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sb
        (S3InvPrefixPlaced A x s0 ∗ coinsCursorAtPlaced x.coinsP x.coins 32 ∗
          A.pool lim (M.stepEvents (dh4OptEvents dh4?) st) sb ∗ stackAt fsp extHookStack ∗
          memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
            (stk - cliInitiateFrame - extHookStack) ∗
          A.live secretsPtr 192 1 ∗
          (secretsPtr ↦ₛ bytesToBv8 (dhPrefix dh1 dh2 dh3 dh4?)) ∗
          dhRemAt secretsPtr dh4? ∗
          memRegion fsp 0x78 ∗ ((fsp + 0x78#64) ↦₆₄ (fsp + 0x3c8#64)) ∗
          stage3KeySlotsAt A.repAlloc fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
          memRegion (fsp + 0x930#64) 8 ∗ memRegion (fsp + 0x938#64) 0x20 ∗
          memRegion (fsp + 0x958#64) 0x48 ∗ ((fsp + 0x9a0#64) ↦ₛ ekASk) ∗
          memRegion (fsp + 0x9c0#64) 0xc40 ∗ memRegion (fsp + 0x1600#64) 24 ∗
          memRegion (fsp + 0x1618#64) 0x648 ∗
          ((fsp + 0x1c60#64) ↦₆₄ 192#64) ∗ ((fsp + 0x1c68#64) ↦₆₄ secretsPtr) ∗
          ((fsp + 0x1c70#64) ↦₆₄ dhLenWord dh4?) ∗ memRegion (fsp + 0x1c78#64) 0x18)
        Q Qp oom) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s
      (S3InvPrefixPlaced A x s0 ∗ coinsCursorAtPlaced x.coinsP x.coins 32 ∗
        A.pool lim st s ∗ stackAt fsp extHookStack ∗
        memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
          (stk - cliInitiateFrame - extHookStack) ∗
        A.live secretsPtr 192 1 ∗ (secretsPtr ↦ₛ bytesToBv8 (F_X25519 ++ dh1 ++ dh2 ++ dh3)) ∗
        memRegion (secretsPtr + 128#64) 32 ∗ memRegion (secretsPtr + 160#64) 32 ∗
        memRegion fsp 0x78 ∗ ((fsp + 0x78#64) ↦₆₄ (fsp + 0x3c8#64)) ∗
        stage3KeySlotsAt A.repAlloc fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
        memRegion (fsp + 0x930#64) 8 ∗ memRegion (fsp + 0x938#64) 0x20 ∗
        memRegion (fsp + 0x958#64) 0x48 ∗ ((fsp + 0x9a0#64) ↦ₛ ekASk) ∗
        memRegion (fsp + 0x9c0#64) 0xc40 ∗ memRegion (fsp + 0x1600#64) 24 ∗
        memRegion (fsp + 0x1618#64) 0x648 ∗
        ((fsp + 0x1c60#64) ↦₆₄ 192#64) ∗ ((fsp + 0x1c68#64) ↦₆₄ secretsPtr) ∗
        ((fsp + 0x1c70#64) ↦₆₄ 128#64) ∗ memRegion (fsp + 0x1c78#64) 0x18)
      Q Qp oom := by
  dsimp only
  set fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
  obtain ⟨_, _, hkpkLen, hopkLen, _, _, _, _⟩ := bundleEOf_props hs3.bundleEq
  have hekASkLen : ekASk.length = 32 := by rw [hs3.ekPairEq.1]; exact List.Vector.toList_length _
  have hekAPkLen : ekAPk.length = 32 := by rw [hs3.ekPairEq.2]; exact List.Vector.toList_length _
  rcases hopk : x.bundle.opk with _ | ⟨oid, ok⟩
  · obtain ⟨halign_n, _, hfsp_n⟩ := hctrl.step_ctx fsp
    refine' s3_block_in_vm_placed hh 0xb6c (Φ := fun sm =>
      sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧
      sm.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
      sm.readReg64 (.gpr 22#5) = fsp + 0x408#64) hctrl ?_ ?_; rotate_left 1
    · have hpc : s.pc = (blkPl_521).base + BitVec.ofNat 64 0xa70 := hctrl.pc
      have hrun := hctrl.run
      dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521, stage3KeySlotsAt, BitVec.ofNat_eq_ofNat] at hpc ⊢
      try simp only [hopk, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
        show (0#32 : BitVec 32).truncate 8 = 0#8 from rfl]
      (try dsimp only [fsp] at *); rw [← hctrl.sp] at *
      try simp only [arm64_norm, wp_norm] at hx20 hx21 hx22
      by_vm_steps (
        wp_steps
        refine s3_done_in_vm (by wp_norm_lhs) (Entails.refl _)
          ⟨by simp only [hx20, hx21, hx22, arm64_norm, wp_norm],
           by simp only [hx20, hx21, hx22, arm64_norm, wp_norm],
           by simp only [hx20, hx21, hx22, arm64_norm, wp_norm]⟩
          (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)))
    · intro sb hvm_b htr_b hctrl_b ⟨hx20_b, hx21_b, hx22_b⟩
      have hpool_b : A.pool lim st s = A.pool lim (M.stepEvents (dh4OptEvents none) st) sb := by
        rw [← stepEvents_dh4OptEvents_none M st]
        exact (A.pool_transport lim st s sb hvm_b).symm
      rw [hctrl.sp] at *; try iterate 6 rw [BitVec.add_comm _ fsp]; try iterate 6 rw [BitVec.add_comm _ (s0.sp - BitVec.ofNat 64 cliInitiateFrame)]
      have hnone_opt := dh4_none_opt ⟨W.C, W.Q⟩ kp x.bundle be x.coins hs3.bundleEq hopk
      have hdh4_eq :
          (none : Option SignalPqxdh.Bytes) =
            ((initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be
              (padCoins x.coins)).bundle.opkB?.map fun (_, opkPk) =>
                (modelPrims X ⟨W.C, W.Q⟩).x25519
                  (initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be
                    (padCoins x.coins)).ekASk opkPk) := by
        rw [hnone_opt]; rfl
      refine sepWPp_conseq_oom ?_
        (hnext sb none hdh4_eq rfl (by intro _ h; nomatch h) hctrl_b (htr_b.trans htr)
          hx20_b hx21_b hx22_b)
      rw [hpool_b]
      dsimp only [dhPrefix, dhRemAt, dhLenWord, stage3KeySlotsAt]
      try simp only [hopk, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
        show (0#32 : BitVec 32).truncate 8 = 0#8 from rfl]
      (try dsimp only [fsp]); sep_frame
  · have hokLen : ok.bytes.toList.length = 32 := hopkLen oid ok hopk
    have hFit_ok :
        FitsEvents M lim st (s3CalcAgreeEvents X W (toU8 ekASk) (toU8 ok.bytes.toList)) := by
      simpa only [s3Dh4CalcAgreeEvents, hopk] using hFit
    obtain ⟨halign_0, _, hfsp_0⟩ := hctrl.step_ctx fsp
    refine' s3_block_to_call_vm_placed hh (lsmpl.base 207)
      0xa94 (Φ := fun sm =>
        sm.readReg64 .x0 = fsp + 0x9a0#64 ∧ sm.readReg64 .x1 = fsp + 0x439#64 ∧
        sm.readReg64 .x8 = fsp + 0x1600#64 ∧
        sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧ sm.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
        sm.readReg64 (.gpr 22#5) = fsp + 0x408#64 ∧ sm.readReg64 (.gpr 26#5) = 128#64)
      hctrl ?_ ?_; rotate_left 1
    · have hpc : s.pc = (blkPl_521).base + BitVec.ofNat 64 0xa70 := hctrl.pc
      have hrun := hctrl.run
      dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521, stage3KeySlotsAt, BitVec.ofNat_eq_ofNat] at hpc ⊢
      try simp only [hopk, Option.isSome_some, ↓reduceIte,
        show (1#32 : BitVec 32).truncate 8 = 1#8 from rfl]
      (try dsimp only [fsp] at *); rw [← hctrl.sp] at *
      try simp only [arm64_norm, wp_norm] at hx20 hx21 hx22 hx26
      by_vm_steps (
        wp_steps
        refine s3_done_call_vm (by wp_norm_lhs) (Entails.refl _)
          ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
           by simp only [hx20, hx21, hx22, hx26, arm64_norm, wp_norm],
           by simp only [hx20, hx21, hx22, hx26, arm64_norm, wp_norm],
           by simp only [hx20, hx21, hx22, hx26, arm64_norm, wp_norm],
           by simp only [hx20, hx21, hx22, hx26, arm64_norm, wp_norm]⟩
          (hpc := by (try wp_norm_goal); try (clear * -; bv_omega))
          (hlr := by (try wp_norm_goal); try (clear * -; bv_omega)))
    · intro sm_c4 hvm_c4 hctrl_c4 hpcm_c4 hlrm_c4 htrm_c4
        ⟨hx0_c4, hx1_c4, hx8_c4, hx20_c4, hx21_c4, hx22_c4, hx26_c4⟩
      have hpool_c4 : A.pool lim st s = A.pool lim st sm_c4 :=
        (A.pool_transport lim st s sm_c4 hvm_c4).symm
      rw [hctrl.sp] at *; try iterate 6 rw [BitVec.add_comm _ fsp]; try iterate 6 rw [BitVec.add_comm _ (s0.sp - BitVec.ofNat 64 cliInitiateFrame)]
      have htr_c4 : sm_c4.trace = s0.trace := htrm_c4.trans htr
      have hsome_opt := dh4_some_eq X ⟨W.C, W.Q⟩ kp x.bundle be x.coins ekASk oid ok
        hs3.bundleEq hopk hs3.ekPairEq.1
      refine s3_calc_agree_of_ok (X := X) hh hCalc
        (fsp + 0x9a0#64) (toU8 ekASk)
        (fsp + 0x439#64) (toU8 ok.bytes.toList) st _
        hctrl_c4 htr_c4 hpcm_c4 hlrm_c4 hx0_c4 hx1_c4 (by rw [hctrl_c4.sp]; exact hx8_c4)
        (by rw [toU8_length_eq, hekASkLen]) (by rw [toU8_length_eq, hokLen]) hFit_ok hpanic
        (by (try dsimp only [stage3KeySlotsAt])
            try simp only [hopk, Option.isSome_some, ↓reduceIte,
              show (1#32 : BitVec 32).truncate 8 = 1#8 from rfl]
            rw [hpool_c4, hctrl_c4.sp, bytesToBv8_toU8_eq, bytesToBv8_toU8_eq]
            (try dsimp only [fsp]); sep_frame)
        ?_ ?_
      · intro hdh4_zero s_z4 hi u2 hctrl_z4 _ htr_z4
        rw [hctrl_c4.sp, ProofLib.pointsTo64_split32_at fsp 0x1600#64 1#64]
        obtain ⟨halign_z4, hx29_z4, hfsp_z4⟩ := hctrl_z4.step_ctx fsp
        refine' s3_block_in_vm_placed hh 0x1544
          (Φ := fun sm => sm.readReg64 (.gpr 26#5) = speWord 10 ∧ sm.readReg64 .x1 = 192#64)
          hctrl_z4 ?_ ?_; rotate_left 1
        · have hpc : s_z4.pc = (blkPl_521).base + BitVec.ofNat 64 0xa94 := hctrl_z4.pc
          have hrun := hctrl_z4.run
          dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521, speWord, BitVec.ofNat_eq_ofNat] at hpc ⊢
          (try dsimp only [fsp] at *); rw [← hctrl_z4.sp] at *
          by_vm_steps (
            wp_steps
            refine s3_done_in_vm (by wp_norm_lhs) (Entails.refl _)
              ⟨by wp_norm_goal, by wp_norm_goal⟩
              (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)))
        · intro sm_u4 hvm_u4 htr_u4 hctrl_u4 ⟨hx26_u4, hx1_u4⟩
          have hpool_u4 : A.pool lim st s_z4 = A.pool lim st sm_u4 :=
            (A.pool_transport lim st s_z4 sm_u4 hvm_u4).symm
          rw [hctrl_z4.sp] at *; rw [← ProofLib.pointsTo64_split32_at fsp 0x1600#64 1#64]
          try iterate 6 rw [BitVec.add_comm _ fsp]; try iterate 6 rw [BitVec.add_comm _ (s0.sp - BitVec.ofNat 64 cliInitiateFrame)]
          have hbad4 : SignalPqxdh.dhOptNonZero
              ((initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be
                (padCoins x.coins)).bundle.opkB?.map fun (_, opkPk) =>
                  (modelPrims X ⟨W.C, W.Q⟩).x25519
                    (initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be
                      (padCoins x.coins)).ekASk opkPk) = false := by
            dsimp only [ofSignalPqxdhPrimitives]; rw [hsome_opt]
            dsimp only [ofSignalPqxdhPrimitives]; rw [hdh4_zero]; rfl
          have hnone := initDef_some_none_of_dh_bad X ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val
            x.bundle be kp x.coins hs3.bundleEq hs3.trustedOk hs3.kpOk
            (Or.inr (Or.inr (Or.inr hbad4)))
          have h128 : (bytesToBv8 (F_X25519 ++ dh1 ++ dh2 ++ dh3)).length = 128 := by
            rw [bytesToBv8_length, List.length_append, List.length_append, List.length_append,
              hdh1_len32, hdh2_len32, hdh3_len32]; decide
          exact s3_dh_unwind_1544_placed hh (hEnv hbad4) hS hnone hstk hstk64 hekAPkLen hekASkLen
            hkpkLen hs3.x8 hsecNonNull hs3.pqspkNonNull hctrl_u4
            (htr_u4.trans (htr_z4.trans htr_c4)) hx26_u4 hx1_u4 hpost hpanic
            (hi ++ 3#8) u2 128#64
            (sepConj_mono (sec128_re_placed secretsPtr (F_X25519 ++ dh1 ++ dh2 ++ dh3) h128)
              (Entails.of_eq (s3_repack4_placed A.repAlloc fsp x.bundle kp ekASk ekAPk pqspkPtr opkId oid ok hopk)))
            (by rw [hpool_u4, bytesToBv8_toU8_eq, bytesToBv8_toU8_eq]
                (try dsimp only [fsp]); cases x.bundle.opk <;> ((try dsimp only); sep_frame))
      · intro hdh4_nz s_ok4 dh4Ptr hctrl_ok4 hcs_ok4 htr_ok4
        rw [hctrl_c4.sp, ProofLib.pointsTo64_split32_at fsp 0x1600#64 0#64]
        let st_a4 := M.stepEvents (rustAllocEvents 32 1) st
        have hx20_4 := hcs_ok4.2.1.trans hx20_c4; have hx21_4 := hcs_ok4.2.2.1.trans hx21_c4
        have hx22_4 := hcs_ok4.2.2.2.1.trans hx22_c4
        have hx26_4 := hcs_ok4.2.2.2.2.2.2.2.1.trans hx26_c4
        set dh4 := (modelPrims X ⟨W.C, W.Q⟩).x25519 (toU8 ekASk) (toU8 ok.bytes.toList)
        have hdh4_len32 : dh4.length = 32 := modelPrims_x25519_len X ⟨W.C, W.Q⟩ _ _
        have hdh4_len : (bytesToBv8 dh4).length = 32 := by rw [bytesToBv8_length, hdh4_len32]
        obtain ⟨halign_4, hx29_4, hfsp_4⟩ := hctrl_ok4.step_ctx fsp
        refine' s3_block_to_call_vm_placed hh (lsρ memcpyName)
          0xb2c (Φ := fun sm =>
            sm.readReg64 .x0 = secretsPtr + 128#64 ∧ sm.readReg64 .x1 = dh4Ptr ∧
            sm.readReg64 .x2 = 32#64 ∧ sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧
            sm.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧ sm.readReg64 (.gpr 22#5) = fsp + 0x408#64 ∧
            sm.readReg64 (.gpr 24#5) = 32#64 ∧ sm.readReg64 (.gpr 25#5) = dh4Ptr ∧
            sm.readReg64 (.gpr 26#5) = 128#64)
          hctrl_ok4 ?_ ?_; rotate_left 1
        · have hpc : s_ok4.pc = (blkPl_521).base + BitVec.ofNat 64 0xa94 := hctrl_ok4.pc
          have hrun := hctrl_ok4.run
          dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521, BitVec.ofNat_eq_ofNat] at hpc ⊢
          (try dsimp only [fsp] at *); rw [← hctrl_ok4.sp] at *
          try simp only [arm64_norm, wp_norm] at hx20_4 hx21_4 hx22_4 hx26_4
          by_vm_steps (
            wp_steps
            refine s3_done_call_vm (by wp_norm_lhs) (Entails.refl _)
              ⟨by simp only [hx20_4, hx21_4, hx22_4, hx26_4, arm64_norm, wp_norm],
               by wp_norm_goal, by wp_norm_goal,
               by simp only [hx20_4, hx21_4, hx22_4, hx26_4, arm64_norm, wp_norm],
               by simp only [hx20_4, hx21_4, hx22_4, hx26_4, arm64_norm, wp_norm],
               by simp only [hx20_4, hx21_4, hx22_4, hx26_4, arm64_norm, wp_norm],
               by wp_norm_goal, by wp_norm_goal,
               by simp only [hx20_4, hx21_4, hx22_4, hx26_4, arm64_norm, wp_norm]⟩
              (hpc := by (try wp_norm_goal); try (clear * -; bv_omega))
              (hlr := by (try wp_norm_goal); try (clear * -; bv_omega)))
        · intro sm_mc4 hvm_mc4 hctrl_mc4 hpcm_mc4 hlrm_mc4 htrm_mc4
            ⟨hx0_mc4, hx1_mc4, hx2_mc4, hx20_mc4, hx21_mc4, hx22_mc4,
             hx24_mc4, hx25_mc4, hx26_mc4⟩
          have hpool_mc4 : A.pool lim st_a4 s_ok4 = A.pool lim st_a4 sm_mc4 :=
            (A.pool_transport lim st_a4 s_ok4 sm_mc4 hvm_mc4).symm
          rw [hctrl_ok4.sp] at *; rw [← ProofLib.pointsTo64_split32_at fsp 0x1600#64 0#64]
          try iterate 6 rw [BitVec.add_comm _ fsp]; try iterate 6 rw [BitVec.add_comm _ (s0.sp - BitVec.ofNat 64 cliInitiateFrame)]
          refine s3_memcpy_pool_placed hh (secretsPtr + 128#64) dh4Ptr (bytesToBv8 dh4) st_a4 _
            hctrl_mc4 (htrm_mc4.trans (htr_ok4.trans htr_c4)) hpcm_mc4 hlrm_mc4
            hx0_mc4 hx1_mc4 (by rw [hx2_mc4, hdh4_len]; decide) hpanic
            (by rw [hpool_mc4, hctrl_mc4.sp, hdh4_len]; (try dsimp only [fsp, st_a4]); sep_frame)
            ?_
          intro s_mc4 hctrl_mc4' hcs_mc4 _ htr_mc4
          rw [hctrl_mc4.sp]
          have hx20_m4 := hcs_mc4.2.1.trans hx20_mc4; have hx21_m4 := hcs_mc4.2.2.1.trans hx21_mc4
          have hx22_m4 := hcs_mc4.2.2.2.1.trans hx22_mc4
          have hx24_m4 := hcs_mc4.2.2.2.2.2.1.trans hx24_mc4
          have hx25_m4 := hcs_mc4.2.2.2.2.2.2.1.trans hx25_mc4
          have hx26_m4 := hcs_mc4.2.2.2.2.2.2.2.1.trans hx26_mc4
          obtain ⟨halign_m4, hx29_m4, hfsp_m4⟩ := hctrl_mc4'.step_ctx fsp
          refine' s3_block_to_call_vm_placed hh (lsρ lsRustDeallocSymCli)
            0xb44 (Φ := fun sm =>
              sm.readReg64 .x0 = dh4Ptr ∧ sm.readReg64 .x1 = 32#64 ∧ sm.readReg64 .x2 = 1#64 ∧
              sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧
              sm.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
              sm.readReg64 (.gpr 22#5) = fsp + 0x408#64)
            hctrl_mc4' ?_ ?_; rotate_left 1
          · have hpc : s_mc4.pc = (blkPl_521).base + BitVec.ofNat 64 0xb2c := hctrl_mc4'.pc
            have hrun := hctrl_mc4'.run
            dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521, BitVec.ofNat_eq_ofNat] at hpc ⊢
            (try dsimp only [fsp] at *); rw [← hctrl_mc4'.sp] at *
            try simp only [arm64_norm, wp_norm]
              at hx20_m4 hx21_m4 hx22_m4 hx24_m4 hx25_m4 hx26_m4
            by_vm_steps (
              wp_steps
              refine s3_done_call_vm (by wp_norm_lhs) (Entails.refl _)
                ⟨by simp only [hx20_m4, hx21_m4, hx22_m4, hx24_m4, hx25_m4, hx26_m4, arm64_norm, wp_norm],
                 by simp only [hx20_m4, hx21_m4, hx22_m4, hx24_m4, hx25_m4, hx26_m4, arm64_norm, wp_norm],
                 by wp_norm_goal,
                 by simp only [hx20_m4, hx21_m4, hx22_m4, hx24_m4, hx25_m4, hx26_m4, arm64_norm, wp_norm],
                 by simp only [hx20_m4, hx21_m4, hx22_m4, hx24_m4, hx25_m4, hx26_m4, arm64_norm, wp_norm],
                 by simp only [hx20_m4, hx21_m4, hx22_m4, hx24_m4, hx25_m4, hx26_m4, arm64_norm, wp_norm]⟩
                (hpc := by (try wp_norm_goal); try (clear * -; bv_omega))
                (hlr := by (try wp_norm_goal); try (clear * -; bv_omega)))
          · intro sm_da4 hvm_da4 hctrl_da4 hpcm_da4 hlrm_da4 htrm_da4
              ⟨hx0_da4, hx1_da4, hx2_da4, hx20_da4, hx21_da4, hx22_da4⟩
            have hpool_da4 : A.pool lim st_a4 s_mc4 = A.pool lim st_a4 sm_da4 :=
              (A.pool_transport lim st_a4 s_mc4 sm_da4 hvm_da4).symm
            rw [hctrl_mc4'.sp] at *; try iterate 6 rw [BitVec.add_comm _ fsp]; try iterate 6 rw [BitVec.add_comm _ (s0.sp - BitVec.ofNat 64 cliInitiateFrame)]
            refine s3_dealloc_stack_placed hh dh4Ptr 32 st_a4 _ hctrl_da4
              hpcm_da4 hlrm_da4 hx0_da4 (by rw [hx1_da4]; decide) (by rw [hx2_da4]; decide)
              lay32
              (by rw [hpool_da4, hctrl_da4.sp]
                  exact sep_replace (pointsToBytes_entails_memRegion_len (a := dh4Ptr) hdh4_len)
                    (by (try dsimp only [fsp, st_a4]); sep_frame)
                    (by (try dsimp only [fsp, st_a4]); sep_frame))
              ?_
            intro s_d4 hctrl_d4 hcs_d4 htr_d4
            rw [hctrl_da4.sp]
            have hx20_d4 := hcs_d4.2.1.trans hx20_da4; have hx21_d4 := hcs_d4.2.2.1.trans hx21_da4
            have hx22_d4 := hcs_d4.2.2.2.1.trans hx22_da4
            refine' s3_block_in_vm_placed hh 0xb6c (Φ := fun sm =>
              sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧
              sm.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
              sm.readReg64 (.gpr 22#5) = fsp + 0x408#64) hctrl_d4 ?_ ?_; rotate_left 1
            · have hpc : s_d4.pc = (blkPl_521).base + BitVec.ofNat 64 0xb44 := hctrl_d4.pc
              have hrun := hctrl_d4.run
              dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521, BitVec.ofNat_eq_ofNat] at hpc ⊢
              (try dsimp only [fsp] at *); rw [← hctrl_d4.sp] at *
              try simp only [arm64_norm, wp_norm] at hx20_d4 hx21_d4 hx22_d4
              by_vm_steps (
                wp_steps
                refine s3_done_in_vm (by wp_norm_lhs) (Entails.refl _)
                  ⟨by simp only [hx20_d4, hx21_d4, hx22_d4, arm64_norm, wp_norm],
                   by simp only [hx20_d4, hx21_d4, hx22_d4, arm64_norm, wp_norm],
                   by simp only [hx20_d4, hx21_d4, hx22_d4, arm64_norm, wp_norm]⟩
                  (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)))
            · intro sb hvm_b htr_b hctrl_b ⟨hx20_b, hx21_b, hx22_b⟩
              have hpool_b :
                  A.pool lim (M.stepEvents (rustDeallocEvents 32 1) st_a4) s_d4 =
                    A.pool lim (M.stepEvents (dh4OptEvents (some dh4)) st) sb := by
                dsimp only [st_a4]
                rw [stepEvents_dh4OptEvents_some M dh4 st]
                exact (A.pool_transport lim (M.stepEvents (dh4OptEvents (some dh4)) st) s_d4 sb hvm_b).symm
              rw [hctrl_d4.sp] at *; try iterate 6 rw [BitVec.add_comm _ fsp]; try iterate 6 rw [BitVec.add_comm _ (s0.sp - BitVec.ofNat 64 cliInitiateFrame)]
              have hdh4_ok : SignalPqxdh.dhOptNonZero (some dh4) = true := by
                simp [SignalPqxdh.dhOptNonZero]; exact hdh4_nz
              have hlen_fn : ∀ d, some dh4 = some d → d.length = 32 := by
                intro d hd; cases hd; exact hdh4_len32
              have htr_fin : sb.trace = s0.trace :=
                htr_b.trans (htr_d4.trans (htrm_da4.trans
                  (htr_mc4.trans (htrm_mc4.trans (htr_ok4.trans htr_c4)))))
              have hsret4 := cells3_to_memRegion24 (fsp + 0x1600#64) 0#64 dh4Ptr 32#64
              have happ4 := append_bv8_at secretsPtr (F_X25519 ++ dh1 ++ dh2 ++ dh3) dh4 128#64
                (by rw [List.length_append, List.length_append, List.length_append,
                      hdh1_len32, hdh2_len32, hdh3_len32]; rfl)
              refine sepWPp_conseq_oom ?_
                (hnext sb (some dh4) hsome_opt.symm hdh4_ok hlen_fn hctrl_b htr_fin
                  hx20_b hx21_b hx22_b)
              dsimp only [dhPrefix, dhRemAt, dhLenWord]
              rw [hpool_b, bytesToBv8_toU8_eq, bytesToBv8_toU8_eq]
              exact sep_replace
                (sepConj_mono hsret4 (sepConj_mono
                  (Entails.of_eq (s3_repack4_placed A.repAlloc fsp x.bundle kp ekASk ekAPk pqspkPtr opkId oid ok hopk))
                  (Entails.of_eq happ4)))
                (by (try dsimp only [fsp]); sep_frame) (by (try dsimp only [fsp]); sep_frame)

theorem dh4_step_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {InitStateEnv : Params → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {st0 st : M.σ} {be : PreKeyBundleFields} {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)} {pqspkPtr secretsPtr : BitVec 64} {opkId : BitVec 32}
    {dh1 dh2 dh3 : SignalPqxdh.Bytes} {stk : Nat} {s0 s3 s : State}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hLocal : InitLocalCalleesPlaced A lim InitStateEnv mmpl gh W stk)
    (hFit : FitsEvents M lim st (s3Dh4CalcAgreeEvents X W ekASk x.bundle.opk))
    (hEnv :
      let P := modelPrims X ⟨W.C, W.Q⟩
      let inp := initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)
      SignalPqxdh.dhOptNonZero (inp.bundle.opkB?.map fun (_, opkPk) => P.x25519 inp.ekASk opkPk) =
        false →
      ∃ evs, InitEnv x evs ∧
        M.stepEvents (rustDeallocEvents 1568 1) (M.stepEvents (rustDeallocEvents 192 1) st) =
          M.stepEvents evs st0)
    (hS : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hs3 : AtStage3Placed W X x be kp ekASk ekAPk pqspkPtr opkId s0 s3)
    (hpost : ∀ sf Pf, InitExitPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Q sf Pf)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf)
    (hdh1_len32 : dh1.length = 32) (hdh2_len32 : dh2.length = 32) (hdh3_len32 : dh3.length = 32)
    (hsecNonNull : secretsPtr ≠ 0#64)
    (hctrl : InInitiatePlaced s0 s 0xa70) (htr : s.trace = s0.trace)
    (hx20 : s.readReg64 (.gpr 20#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x348#64)
    (hx21 : s.readReg64 (.gpr 21#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x388#64)
    (hx22 : s.readReg64 (.gpr 22#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x408#64)
    (hx26 : s.readReg64 (.gpr 26#5) = 128#64)
    (hnext : ∀ (sb : State) (dh4? : Option SignalPqxdh.Bytes),
      let P := modelPrims X ⟨W.C, W.Q⟩
      let inp := initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)
      let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
      dh4? = (inp.bundle.opkB?.map fun (_, opkPk) => P.x25519 inp.ekASk opkPk) →
      SignalPqxdh.dhOptNonZero dh4? = true →
      (∀ d, dh4? = some d → d.length = 32) →
      InInitiatePlaced s0 sb 0xb6c → sb.trace = s0.trace →
      sb.readReg64 (.gpr 20#5) = fsp + 0x348#64 → sb.readReg64 (.gpr 21#5) = fsp + 0x388#64 →
      sb.readReg64 (.gpr 22#5) = fsp + 0x408#64 →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sb
        (S3InvPrefixPlaced A x s0 ∗ coinsCursorAtPlaced x.coinsP x.coins 32 ∗
          A.pool lim (M.stepEvents (dh4OptEvents dh4?) st) sb ∗ stackAt fsp extHookStack ∗
          memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
            (stk - cliInitiateFrame - extHookStack) ∗
          A.live secretsPtr 192 1 ∗
          (secretsPtr ↦ₛ bytesToBv8 (dhPrefix dh1 dh2 dh3 dh4?)) ∗
          dhRemAt secretsPtr dh4? ∗
          memRegion fsp 0x78 ∗ ((fsp + 0x78#64) ↦₆₄ (fsp + 0x3c8#64)) ∗
          stage3KeySlotsAt A.repAlloc fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
          memRegion (fsp + 0x930#64) 8 ∗ memRegion (fsp + 0x938#64) 0x20 ∗
          memRegion (fsp + 0x958#64) 0x48 ∗ ((fsp + 0x9a0#64) ↦ₛ ekASk) ∗
          memRegion (fsp + 0x9c0#64) 0xc40 ∗ memRegion (fsp + 0x1600#64) 24 ∗
          memRegion (fsp + 0x1618#64) 0x648 ∗
          ((fsp + 0x1c60#64) ↦₆₄ 192#64) ∗ ((fsp + 0x1c68#64) ↦₆₄ secretsPtr) ∗
          ((fsp + 0x1c70#64) ↦₆₄ dhLenWord dh4?) ∗ memRegion (fsp + 0x1c78#64) 0x18)
        Q Qp oom) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s
      (S3InvPrefixPlaced A x s0 ∗ coinsCursorAtPlaced x.coinsP x.coins 32 ∗
        A.pool lim st s ∗ stackAt fsp extHookStack ∗
        memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
          (stk - cliInitiateFrame - extHookStack) ∗
        A.live secretsPtr 192 1 ∗ (secretsPtr ↦ₛ bytesToBv8 (F_X25519 ++ dh1 ++ dh2 ++ dh3)) ∗
        memRegion (secretsPtr + 128#64) 32 ∗ memRegion (secretsPtr + 160#64) 32 ∗
        memRegion fsp 0x78 ∗ ((fsp + 0x78#64) ↦₆₄ (fsp + 0x3c8#64)) ∗
        stage3KeySlotsAt A.repAlloc fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
        memRegion (fsp + 0x930#64) 8 ∗ memRegion (fsp + 0x938#64) 0x20 ∗
        memRegion (fsp + 0x958#64) 0x48 ∗ ((fsp + 0x9a0#64) ↦ₛ ekASk) ∗
        memRegion (fsp + 0x9c0#64) 0xc40 ∗ memRegion (fsp + 0x1600#64) 24 ∗
        memRegion (fsp + 0x1618#64) 0x648 ∗
        ((fsp + 0x1c60#64) ↦₆₄ 192#64) ∗ ((fsp + 0x1c68#64) ↦₆₄ secretsPtr) ∗
        ((fsp + 0x1c70#64) ↦₆₄ 128#64) ∗ memRegion (fsp + 0x1c78#64) 0x18)
      Q Qp oom :=
  dh4_step_of_ok hh (hLocal.calculateAgreement X) hFit hEnv hS hstk hstk64 hs3 hpost hpanic
    hdh1_len32 hdh2_len32 hdh3_len32 hsecNonNull hctrl htr hx20 hx21 hx22 hx26 hnext

theorem dh4_step_hooks_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {st0 st : M.σ} {be : PreKeyBundleFields} {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)} {pqspkPtr secretsPtr : BitVec 64} {opkId : BitVec 32}
    {dh1 dh2 dh3 : SignalPqxdh.Bytes} {stk : Nat} {s0 s3 s : State}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hFit : FitsEvents M lim st (s3Dh4CalcAgreeEvents X W ekASk x.bundle.opk))
    (hEnv :
      let P := modelPrims X ⟨W.C, W.Q⟩
      let inp := initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)
      SignalPqxdh.dhOptNonZero (inp.bundle.opkB?.map fun (_, opkPk) => P.x25519 inp.ekASk opkPk) =
        false →
      ∃ evs, InitEnv x evs ∧
        M.stepEvents (rustDeallocEvents 1568 1) (M.stepEvents (rustDeallocEvents 192 1) st) =
          M.stepEvents evs st0)
    (hS : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hs3 : AtStage3Placed W X x be kp ekASk ekAPk pqspkPtr opkId s0 s3)
    (hpost : ∀ sf Pf, InitExitPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Q sf Pf)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf)
    (hdh1_len32 : dh1.length = 32) (hdh2_len32 : dh2.length = 32) (hdh3_len32 : dh3.length = 32)
    (hsecNonNull : secretsPtr ≠ 0#64)
    (hctrl : InInitiatePlaced s0 s 0xa70) (htr : s.trace = s0.trace)
    (hx20 : s.readReg64 (.gpr 20#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x348#64)
    (hx21 : s.readReg64 (.gpr 21#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x388#64)
    (hx22 : s.readReg64 (.gpr 22#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x408#64)
    (hx26 : s.readReg64 (.gpr 26#5) = 128#64)
    (hnext : ∀ (sb : State) (dh4? : Option SignalPqxdh.Bytes),
      let P := modelPrims X ⟨W.C, W.Q⟩
      let inp := initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)
      let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
      dh4? = (inp.bundle.opkB?.map fun (_, opkPk) => P.x25519 inp.ekASk opkPk) →
      SignalPqxdh.dhOptNonZero dh4? = true →
      (∀ d, dh4? = some d → d.length = 32) →
      InInitiatePlaced s0 sb 0xb6c → sb.trace = s0.trace →
      sb.readReg64 (.gpr 20#5) = fsp + 0x348#64 → sb.readReg64 (.gpr 21#5) = fsp + 0x388#64 →
      sb.readReg64 (.gpr 22#5) = fsp + 0x408#64 →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sb
        (S3InvPrefixPlaced A x s0 ∗ coinsCursorAtPlaced x.coinsP x.coins 32 ∗
          A.pool lim (M.stepEvents (dh4OptEvents dh4?) st) sb ∗ stackAt fsp extHookStack ∗
          memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
            (stk - cliInitiateFrame - extHookStack) ∗
          A.live secretsPtr 192 1 ∗
          (secretsPtr ↦ₛ bytesToBv8 (dhPrefix dh1 dh2 dh3 dh4?)) ∗
          dhRemAt secretsPtr dh4? ∗
          memRegion fsp 0x78 ∗ ((fsp + 0x78#64) ↦₆₄ (fsp + 0x3c8#64)) ∗
          stage3KeySlotsAt A.repAlloc fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
          memRegion (fsp + 0x930#64) 8 ∗ memRegion (fsp + 0x938#64) 0x20 ∗
          memRegion (fsp + 0x958#64) 0x48 ∗ ((fsp + 0x9a0#64) ↦ₛ ekASk) ∗
          memRegion (fsp + 0x9c0#64) 0xc40 ∗ memRegion (fsp + 0x1600#64) 24 ∗
          memRegion (fsp + 0x1618#64) 0x648 ∗
          ((fsp + 0x1c60#64) ↦₆₄ 192#64) ∗ ((fsp + 0x1c68#64) ↦₆₄ secretsPtr) ∗
          ((fsp + 0x1c70#64) ↦₆₄ dhLenWord dh4?) ∗ memRegion (fsp + 0x1c78#64) 0x18)
        Q Qp oom) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s
      (S3InvPrefixPlaced A x s0 ∗ coinsCursorAtPlaced x.coinsP x.coins 32 ∗
        A.pool lim st s ∗ stackAt fsp extHookStack ∗
        memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
          (stk - cliInitiateFrame - extHookStack) ∗
        A.live secretsPtr 192 1 ∗ (secretsPtr ↦ₛ bytesToBv8 (F_X25519 ++ dh1 ++ dh2 ++ dh3)) ∗
        memRegion (secretsPtr + 128#64) 32 ∗ memRegion (secretsPtr + 160#64) 32 ∗
        memRegion fsp 0x78 ∗ ((fsp + 0x78#64) ↦₆₄ (fsp + 0x3c8#64)) ∗
        stage3KeySlotsAt A.repAlloc fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
        memRegion (fsp + 0x930#64) 8 ∗ memRegion (fsp + 0x938#64) 0x20 ∗
        memRegion (fsp + 0x958#64) 0x48 ∗ ((fsp + 0x9a0#64) ↦ₛ ekASk) ∗
        memRegion (fsp + 0x9c0#64) 0xc40 ∗ memRegion (fsp + 0x1600#64) 24 ∗
        memRegion (fsp + 0x1618#64) 0x648 ∗
        ((fsp + 0x1c60#64) ↦₆₄ 192#64) ∗ ((fsp + 0x1c68#64) ↦₆₄ secretsPtr) ∗
        ((fsp + 0x1c70#64) ↦₆₄ 128#64) ∗ memRegion (fsp + 0x1c78#64) 0x18)
      Q Qp oom :=
  dh4_step_of_ok hh (calculateAgreement_cli_placed_ok mmpl gh W hh X) hFit hEnv hS hstk hstk64 hs3
    hpost hpanic hdh1_len32 hdh2_len32 hdh3_len32 hsecNonNull hctrl htr hx20 hx21 hx22 hx26 hnext

theorem dh4_step_placed_evs_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {InitStateEnv : Params → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {st0 : M.σ} {evs_pre : List AllocEvent}
    {be : PreKeyBundleFields} {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)} {pqspkPtr secretsPtr : BitVec 64} {opkId : BitVec 32}
    {dh1 dh2 dh3 : SignalPqxdh.Bytes} {stk : Nat} {s0 s3 s : State}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hLocal : InitLocalCalleesPlaced A lim InitStateEnv mmpl gh W stk)
    (hFit : x.bundle.opk.isSome = true →
      FitsEvents M lim (M.stepEvents evs_pre st0) (rustAllocEvents 32 1))
    (hEnv :
      let P := modelPrims X ⟨W.C, W.Q⟩
      let inp := initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)
      SignalPqxdh.dhOptNonZero (inp.bundle.opkB?.map fun (_, opkPk) => P.x25519 inp.ekASk opkPk) =
        false →
      InitEnv x (evs_pre ++ unwind1548Events))
    (hS : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hs3 : AtStage3Placed W X x be kp ekASk ekAPk pqspkPtr opkId s0 s3)
    (hpost : ∀ sf Pf, InitExitPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Q sf Pf)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf)
    (hdh1_len32 : dh1.length = 32) (hdh2_len32 : dh2.length = 32) (hdh3_len32 : dh3.length = 32)
    (hsecNonNull : secretsPtr ≠ 0#64)
    (hctrl : InInitiatePlaced s0 s 0xa70) (htr : s.trace = s0.trace)
    (hx20 : s.readReg64 (.gpr 20#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x348#64)
    (hx21 : s.readReg64 (.gpr 21#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x388#64)
    (hx22 : s.readReg64 (.gpr 22#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x408#64)
    (hx26 : s.readReg64 (.gpr 26#5) = 128#64)
    (hnext : ∀ (sb : State) (dh4? : Option SignalPqxdh.Bytes),
      let P := modelPrims X ⟨W.C, W.Q⟩
      let inp := initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)
      let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
      dh4? = (inp.bundle.opkB?.map fun (_, opkPk) => P.x25519 inp.ekASk opkPk) →
      SignalPqxdh.dhOptNonZero dh4? = true →
      (∀ d, dh4? = some d → d.length = 32) →
      InInitiatePlaced s0 sb 0xb6c → sb.trace = s0.trace →
      sb.readReg64 (.gpr 20#5) = fsp + 0x348#64 → sb.readReg64 (.gpr 21#5) = fsp + 0x388#64 →
      sb.readReg64 (.gpr 22#5) = fsp + 0x408#64 →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sb
        (S3InvPrefixPlaced A x s0 ∗ coinsCursorAtPlaced x.coinsP x.coins 32 ∗
          A.pool lim (M.stepEvents (evs_pre ++ dh4OptEvents dh4?) st0) sb ∗ stackAt fsp extHookStack ∗
          memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
            (stk - cliInitiateFrame - extHookStack) ∗
          A.live secretsPtr 192 1 ∗
          (secretsPtr ↦ₛ bytesToBv8 (dhPrefix dh1 dh2 dh3 dh4?)) ∗
          dhRemAt secretsPtr dh4? ∗
          memRegion fsp 0x78 ∗ ((fsp + 0x78#64) ↦₆₄ (fsp + 0x3c8#64)) ∗
          stage3KeySlotsAt A.repAlloc fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
          memRegion (fsp + 0x930#64) 8 ∗ memRegion (fsp + 0x938#64) 0x20 ∗
          memRegion (fsp + 0x958#64) 0x48 ∗ ((fsp + 0x9a0#64) ↦ₛ ekASk) ∗
          memRegion (fsp + 0x9c0#64) 0xc40 ∗ memRegion (fsp + 0x1600#64) 24 ∗
          memRegion (fsp + 0x1618#64) 0x648 ∗
          ((fsp + 0x1c60#64) ↦₆₄ 192#64) ∗ ((fsp + 0x1c68#64) ↦₆₄ secretsPtr) ∗
          ((fsp + 0x1c70#64) ↦₆₄ dhLenWord dh4?) ∗ memRegion (fsp + 0x1c78#64) 0x18)
        Q Qp oom) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s
      (S3InvPrefixPlaced A x s0 ∗ coinsCursorAtPlaced x.coinsP x.coins 32 ∗
        A.pool lim (M.stepEvents evs_pre st0) s ∗ stackAt fsp extHookStack ∗
        memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
          (stk - cliInitiateFrame - extHookStack) ∗
        A.live secretsPtr 192 1 ∗ (secretsPtr ↦ₛ bytesToBv8 (F_X25519 ++ dh1 ++ dh2 ++ dh3)) ∗
        memRegion (secretsPtr + 128#64) 32 ∗ memRegion (secretsPtr + 160#64) 32 ∗
        memRegion fsp 0x78 ∗ ((fsp + 0x78#64) ↦₆₄ (fsp + 0x3c8#64)) ∗
        stage3KeySlotsAt A.repAlloc fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
        memRegion (fsp + 0x930#64) 8 ∗ memRegion (fsp + 0x938#64) 0x20 ∗
        memRegion (fsp + 0x958#64) 0x48 ∗ ((fsp + 0x9a0#64) ↦ₛ ekASk) ∗
        memRegion (fsp + 0x9c0#64) 0xc40 ∗ memRegion (fsp + 0x1600#64) 24 ∗
        memRegion (fsp + 0x1618#64) 0x648 ∗
        ((fsp + 0x1c60#64) ↦₆₄ 192#64) ∗ ((fsp + 0x1c68#64) ↦₆₄ secretsPtr) ∗
        ((fsp + 0x1c70#64) ↦₆₄ 128#64) ∗ memRegion (fsp + 0x1c78#64) 0x18)
      Q Qp oom := by
  refine dh4_step_placed_ok hh hLocal (fitsEvents_s3Dh4CalcAgreeEvents hFit)
    (fun hbad => ⟨evs_pre ++ unwind1548Events, hEnv hbad,
      (stepEvents_unwind1548Events M (M.stepEvents evs_pre st0)).trans
        (M.stepEvents_append evs_pre unwind1548Events st0).symm⟩)
    hS hstk hstk64 hs3 hpost hpanic hdh1_len32 hdh2_len32 hdh3_len32 hsecNonNull hctrl htr
    hx20 hx21 hx22 hx26 fun sb dh4? hdh4 hnz hlen hc hb hx20' hx21' hx22' => ?_
  rw [← M.stepEvents_append evs_pre (dh4OptEvents dh4?) st0]
  exact hnext sb dh4? hdh4 hnz hlen hc hb hx20' hx21' hx22'

end

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.DhStepsCPlacedBudget
