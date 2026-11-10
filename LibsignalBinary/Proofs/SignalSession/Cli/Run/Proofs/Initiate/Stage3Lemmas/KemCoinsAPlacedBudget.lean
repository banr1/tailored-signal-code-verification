/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.KemCoinsAPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.KemCoinsHelpersPlacedBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Budget-Threaded Stage 3 KEM Seed Unroll Part A (`[LibsignalPlacement]`, `+0x0b6c → +0x0c48`)

Advances `+0x0b6c → +0x0c48` across `memcpy(fsp + 0x9c0, pqspkPtr, 1568)` and 4-byte coin draws
`0..6` under `RustCliAllocBudget M` (`0` heap events).
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
open CryptoVerification (LibsignalPlacement lsmpl lsρ)
open CryptoVerification.CliHandshake.InitiatePlaced (blkPl_521 lsProg_521)
open CryptoVerification.E2E (PreKeyBundleFields UnreachedPqxdhPrimitives)
open CryptoVerification.E2E.Pqxdh.Initiator (bytesToBv8)
open CryptoVerification.E2E.Pqxdh.ResponderCore (and_ff32_hi56_3 and_ff_hi56_3 extractLsb_hi56_3 zext64_trunc32_hi56_3_and_ff)
open CryptoVerification.LibsignalPublicApi.StoreKit (withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet (extHookStack memcpyName)
open CryptoVerification.RecordCodecs (IdentityKeyPair)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced)
open CryptoVerification.SignalSession.Cli.RunCompose (InitGhost RunSem)
open CryptoVerification.SignalSession.Cli.RunProofs (cliInitiateFrame cliInitiateNeed padCoins)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate
  (AtStage3Placed InInitiatePlaced cliCoinsFillStack cliCoinsFillStackPlaced coinsCursorAtPlaced
   initPcPlaced initProgPlaced stage3KeySlotsAt stk_sub_ge_base)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage3Lemmas
  (bundleEOf_props coinWord dhLenWord dhPrefix dhRemAt memRegion_merge_at sepWPp_conseq_oom
   sepWPp_exists_elim_oom sep_replace stackAt_sub_split_init stk_sub_le_2pow64)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.KemCoinsAPlacedBudget

noncomputable section

open Arm64 Arm64.Obj Arm64.Process ProofLib SepProp
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget VmPreserved)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.CoinsFillPlacedBudget
  (coinsFillSpecPlacedW3)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.DefsPlacedBudget
  (InitPanicPostPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlacedBudget
  (RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.CollapsePlacedBudget
  (s3_block_to_call_vm_placed s3_done_call_vm)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.DefsPlacedBudget
  (s3_memcpy_pool_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.DhHelpersPlacedBudget
  (S3InvPrefixPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.KemCoinsHelpersPlacedBudget
  (coinsFill_cli_placed_ok s3_coins_fill4_placed_at s3_draw_to_slot_placed_at
   s3_step_b6c_b8c_placed s3_step_b8c_ba0_placed)
open Arm64.Obj (MultiPlacement)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate (initProgExtPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (CliGhostHooks cliGhostExterns)

attribute [local irreducible] Program.fetch Program.externAt? S3InvPrefixPlaced coinsCursorAtPlaced
  coinWord padCoins dhPrefix dhRemAt
attribute [local simp, local arm64_norm, local wp_norm]
  extractLsb_hi56_3 and_ff_hi56_3 and_ff32_hi56_3 zext64_trunc32_hi56_3_and_ff

private theorem scratch120_split (fsp : BitVec 64) :
    memRegion fsp 0x78 =
      memRegion fsp 8 ∗ memRegion (fsp + 0x68#64) 4 ∗ memRegion (fsp + 0x60#64) 4 ∗
      memRegion (fsp + 0x5c#64) 4 ∗ memRegion (fsp + 0x58#64) 4 ∗ memRegion (fsp + 0x54#64) 4 ∗
      memRegion (fsp + 0x50#64) 4 ∗ memRegion (fsp + 0x4c#64) 4 ∗ memRegion (fsp + 0x48#64) 4 ∗
      memRegion (fsp + 0x44#64) 4 ∗ memRegion (fsp + 0x40#64) 4 ∗ memRegion (fsp + 0x3c#64) 4 ∗
      memRegion (fsp + 0x38#64) 4 ∗ memRegion (fsp + 0x34#64) 4 ∗ memRegion (fsp + 0x30#64) 4 ∗
      memRegion (fsp + 0x2c#64) 4 ∗ memRegion (fsp + 0x28#64) 4 ∗ memRegion (fsp + 0x24#64) 4 ∗
      memRegion (fsp + 0x20#64) 4 ∗ memRegion (fsp + 0x1c#64) 4 ∗ memRegion (fsp + 0x18#64) 4 ∗
      memRegion (fsp + 0x14#64) 4 ∗ memRegion (fsp + 0x10#64) 4 ∗ memRegion (fsp + 0x0c#64) 4 ∗
      memRegion (fsp + 0x08#64) 4 ∗ memRegion (fsp + 0x64#64) 4 ∗ memRegion (fsp + 0x6c#64) 4 ∗
      memRegion (fsp + 0x70#64) 8 := by
  rw [← memRegion_merge_at fsp 8 112 (fsp + 0x08#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x08#64) 4 108 (fsp + 0x0c#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x0c#64) 4 104 (fsp + 0x10#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x10#64) 4 100 (fsp + 0x14#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x14#64) 4 96 (fsp + 0x18#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x18#64) 4 92 (fsp + 0x1c#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x1c#64) 4 88 (fsp + 0x20#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x20#64) 4 84 (fsp + 0x24#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x24#64) 4 80 (fsp + 0x28#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x28#64) 4 76 (fsp + 0x2c#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x2c#64) 4 72 (fsp + 0x30#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x30#64) 4 68 (fsp + 0x34#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x34#64) 4 64 (fsp + 0x38#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x38#64) 4 60 (fsp + 0x3c#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x3c#64) 4 56 (fsp + 0x40#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x40#64) 4 52 (fsp + 0x44#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x44#64) 4 48 (fsp + 0x48#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x48#64) 4 44 (fsp + 0x4c#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x4c#64) 4 40 (fsp + 0x50#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x50#64) 4 36 (fsp + 0x54#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x54#64) 4 32 (fsp + 0x58#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x58#64) 4 28 (fsp + 0x5c#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x5c#64) 4 24 (fsp + 0x60#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x60#64) 4 20 (fsp + 0x64#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x64#64) 4 16 (fsp + 0x68#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x68#64) 4 12 (fsp + 0x6c#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x6c#64) 4 8 (fsp + 0x70#64) (by bv_omega) (by decide)]
  sep_ac_rfl

private theorem kem_locals_9c0 (fsp : BitVec 64) :
    memRegion (fsp + 0x9c0#64) 0xc40 =
      memRegion (fsp + 0x9c0#64) 1568 ∗ memRegion (fsp + 0xfe0#64) 32 ∗
      memRegion (fsp + 0x1000#64) 0x600 := by
  rw [← memRegion_merge_at (fsp + 0x9c0#64) 1568 1568 (fsp + 0xfe0#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0xfe0#64) 32 0x600 (fsp + 0x1000#64) (by bv_omega) (by decide)]

private theorem kem_locals_1600 (fsp : BitVec 64) :
    memRegion (fsp + 0x1600#64) 24 =
      memRegion (fsp + 0x1600#64) 4 ∗ memRegion (fsp + 0x1604#64) 20 := by
  rw [← memRegion_merge_at (fsp + 0x1600#64) 4 20 (fsp + 0x1604#64) (by bv_omega) (by decide)]

private theorem mem4_elim_word {prog : Program} {ret : BitVec 64} {s : State}
    {a : BitVec 64} {B R : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : ∀ z : BitVec 32, SepWPp prog ret s (B ∗ ((a ↦₃₂ z) ∗ R)) Q Qp oom) :
    SepWPp prog ret s ((memRegion a 4 ∗ B) ∗ R) Q Qp oom := by
  rw [sepConj_assoc, ProofLib.memRegion_four a, sepExists_sepConj_left]
  exact sepWPp_exists_elim_oom fun z =>
    sepWPp_conseq_oom
      (Entails.of_eq (by rw [← sepConj_assoc, sepConj_comm (a ↦₃₂ z) B, sepConj_assoc])) (h z)

private theorem mem8_elim_word {prog : Program} {ret : BitVec 64} {s : State}
    {a : BitVec 64} {B R : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : ∀ z : BitVec 64, SepWPp prog ret s (B ∗ ((a ↦₆₄ z) ∗ R)) Q Qp oom) :
    SepWPp prog ret s ((memRegion a 8 ∗ B) ∗ R) Q Qp oom := by
  rw [sepConj_assoc, ProofLib.memRegion_eight a, sepExists_sepConj_left]
  exact sepWPp_exists_elim_oom fun z =>
    sepWPp_conseq_oom
      (Entails.of_eq (by rw [← sepConj_assoc, sepConj_comm (a ↦₆₄ z) B, sepConj_assoc])) (h z)

private theorem s3_repack_kpk {R : RustAlloc} (fsp : BitVec 64) (x : InitGhost)
    (kp : IdentityKeyPair) (ekASk ekAPk : List (BitVec 8)) (pqspkPtr : BitVec 64)
    (opkId : BitVec 32) :
    ((let opkFlag : BitVec 32 := if x.bundle.opk.isSome then 1#32 else 0#32
      ((fsp + 0x298#64) ↦ₛ ekAPk) ∗ memRegion (fsp + 0x2b8#64) 0x48 ∗
      ((fsp + 0x300#64) ↦₃₂ opkFlag) ∗ ((fsp + 0x304#64) ↦₃₂ opkId) ∗
      memRegion (fsp + 0x308#64) 0x40 ∗
      ((fsp + 0x348#64) ↦ₛ kp.identityKey.publicKey.bytes.toList) ∗
      ((fsp + 0x368#64) ↦ₛ kp.privateKey.bytes.toList) ∗
      ((fsp + 0x388#64) ↦ₛ ekAPk) ∗ ((fsp + 0x3a8#64) ↦ₛ ekASk) ∗
      ((fsp + 0x3c8#64) ↦ₛ x.bundle.idKey.publicKey.bytes.toList) ∗
      ((fsp + 0x3e8#64) ↦ₛ x.bundle.spk.bytes.toList) ∗
      ((fsp + 0x408#64) ↦ₛ x.bundle.spk.bytes.toList) ∗
      ((fsp + 0x428#64) ↦₆₄ pqspkPtr) ∗ ((fsp + 0x430#64) ↦₆₄ 1568#64) ∗
      R.live pqspkPtr 1568 1 ∗
      ((fsp + 0x438#64) ↦₈ opkFlag.truncate 8) ∗
      (match x.bundle.opk with
       | some (_, k) => (fsp + 0x439#64) ↦ₛ k.bytes.toList
       | none => memRegion (fsp + 0x439#64) 32) ∗
      ((fsp + 0x459#64) ↦₈ 0#8) ∗ memRegion (fsp + 0x45a#64) 6) ∗
     (pqspkPtr ↦ₛ x.bundle.kpk)) =
    stage3KeySlotsAt R fsp x.bundle kp ekASk ekAPk pqspkPtr opkId := by
  dsimp only [stage3KeySlotsAt]
  rcases x.bundle.opk with _ | ⟨_, k⟩ <;>
    (simp only [Option.isSome_none, Option.isSome_some, Bool.false_eq_true, ↓reduceIte]; sep_ac_rfl)

private theorem s3_coins_fill4_pool_at [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {S : RunSem} {x : InitGhost} {st0 : M.σ} {stk : Nat}
    (cfStk : Nat)
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hCall : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 618)
      (withLsCodeRoLoaded lsmpl (coinsFillSpecPlacedW3 cfStk)))
    (hcoinsLt : x.coins.length < 2 ^ 63)
    (i : Nat) (hi : i < 32) (st : M.σ) (F : SepProp)
    {s0 s : State} {k_in k_out : Nat} {P : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hctrl : InInitiatePlaced s0 s k_in) (htr : s.trace = s0.trace)
    (hpc : s.pc = lsmpl.base 618)
    (hlr : s.readReg64 .lr = initPcPlaced k_out)
    (hx0 : s.readReg64 .x0 = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x1600#64)
    (hx1 : s.readReg64 .x1 = 4#64)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf)
    (hpre : P ⊢
      A.pool lim st s ∗ coinsCursorAtPlaced x.coinsP x.coins (32 + 4 * i) ∗
        (((s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x1600#64) ↦₃₂ 0#32) ∗
        stackAt s.sp cfStk ∗ F)
    (hnext : ∀ sm : State,
      InInitiatePlaced s0 sm k_out → CalleeSavedPreserved s sm → sm.trace = s.trace →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sm
        (A.pool lim st sm ∗ coinsCursorAtPlaced x.coinsP x.coins (32 + 4 * (i + 1)) ∗
          (((s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x1600#64) ↦₃₂
            coinWord (padCoins x.coins) i hi) ∗
          stackAt s.sp cfStk ∗ F) Q Qp oom) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s P Q Qp oom := by
  refine s3_coins_fill4_placed_at cfStk hh hCall hcoinsLt i hi (A.pool lim st s ∗ F)
    hctrl htr hpc hlr hx0 hx1 hpanic
    (Entails.trans hpre (Entails.of_eq (by sep_ac_rfl))) ?_
  intro sm hctrl' hcsm hvm htrm
  have hpool : A.pool lim st s = A.pool lim st sm := (A.pool_transport lim st s sm hvm).symm
  exact sepWPp_conseq_oom
    (Entails.of_eq (by rw [hpool]; sep_ac_rfl))
    (hnext sm hctrl' hcsm htrm)

private theorem s3_draw_pool_at [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {S : RunSem} {x : InitGhost} {st0 : M.σ} {stk : Nat}
    (cfStk : Nat)
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hCall : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 618)
      (withLsCodeRoLoaded lsmpl (coinsFillSpecPlacedW3 cfStk)))
    (hcoinsLt : x.coins.length < 2 ^ 63)
    (i : Nat) (hi_prev : i - 1 < 32) (hi : i < 32)
    (k_in k_out : Nat) (slotOff : BitVec 64) (oldSlot : BitVec 32) (st : M.σ) (F : SepProp)
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hctrl : InInitiatePlaced s0 s k_in) (htr : s.trace = s0.trace)
    (hx20 : s.readReg64 (.gpr 20#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x348#64)
    (hx21 : s.readReg64 (.gpr 21#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x388#64)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf)
    (hstep : ∀ (G : SepProp),
      (s.sp &&& 15#64 == 0#64) = true →
      s.pc = (blkPl_521).base + BitVec.ofNat 64 k_in →
      s.status = .Running →
      s.readReg64 (.gpr 20#5) = s.sp + 0x348#64 →
      s.readReg64 (.gpr 21#5) = s.sp + 0x388#64 →
      SepWP (initProgPlaced mmpl gh W) (lsmpl.base 618) s
        (coinsCursorAtPlaced x.coinsP x.coins (32 + 4 * i) ∗
          ((s.sp + 0x1600#64) ↦₃₂ coinWord (padCoins x.coins) (i - 1) hi_prev) ∗
          ((s.sp + slotOff) ↦₃₂ oldSlot) ∗
          stackAt s.sp cfStk ∗ G)
        (fun sm Pm =>
          VmPreserved s sm ∧
          sm.trace = s.trace ∧
          (Pm ⊢
            coinsCursorAtPlaced x.coinsP x.coins (32 + 4 * i) ∗
              ((s.sp + 0x1600#64) ↦₃₂ 0#32) ∗
              ((s.sp + slotOff) ↦₃₂ coinWord (padCoins x.coins) (i - 1) hi_prev) ∗
              stackAt s.sp cfStk ∗ G) ∧
          sm.sp = s.sp ∧ sm.readReg64 .fp = s.readReg64 .fp ∧
          sm.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) ∧
          calleeSavedVRegs sm = calleeSavedVRegs s ∧
          sm.readReg64 .lr = (blkPl_521).base + BitVec.ofNat 64 k_out ∧
          (sm.readReg64 .x0 = s.sp + 0x1600#64 ∧ sm.readReg64 .x1 = 4#64 ∧
            sm.readReg64 (.gpr 20#5) = s.sp + 0x348#64 ∧
            sm.readReg64 (.gpr 21#5) = s.sp + 0x388#64)))
    (hpre : P ⊢
      A.pool lim st s ∗ coinsCursorAtPlaced x.coinsP x.coins (32 + 4 * i) ∗
        (((s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x1600#64) ↦₃₂
          coinWord (padCoins x.coins) (i - 1) hi_prev) ∗
        (((s0.sp - BitVec.ofNat 64 cliInitiateFrame) + slotOff) ↦₃₂ oldSlot) ∗
        stackAt (s0.sp - BitVec.ofNat 64 cliInitiateFrame) cfStk ∗ F)
    (hnext : ∀ sm : State,
      InInitiatePlaced s0 sm k_out → sm.trace = s0.trace →
      sm.readReg64 (.gpr 20#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x348#64 →
      sm.readReg64 (.gpr 21#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x388#64 →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sm
        (A.pool lim st sm ∗ coinsCursorAtPlaced x.coinsP x.coins (32 + 4 * (i + 1)) ∗
          (((s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x1600#64) ↦₃₂
            coinWord (padCoins x.coins) i hi) ∗
          stackAt (s0.sp - BitVec.ofNat 64 cliInitiateFrame) cfStk ∗
          (((s0.sp - BitVec.ofNat 64 cliInitiateFrame) + slotOff) ↦₃₂
            coinWord (padCoins x.coins) (i - 1) hi_prev) ∗ F)
        Q Qp oom) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s P Q Qp oom := by
  refine s3_draw_to_slot_placed_at cfStk hh hCall hcoinsLt i hi_prev hi k_in k_out slotOff oldSlot
    (A.pool lim st s ∗ F) hctrl htr hx20 hx21 hpanic hstep
    (Entails.trans hpre (Entails.of_eq (by sep_ac_rfl))) ?_
  intro sm; dsimp only; intro hctrl' hvm htr' hx20' hx21'
  have hpool : A.pool lim st s = A.pool lim st sm := (A.pool_transport lim st s sm hvm).symm
  exact sepWPp_conseq_oom
    (Entails.of_eq (by rw [hpool]; sep_ac_rfl))
    (hnext sm hctrl' htr' hx20' hx21')

set_option maxHeartbeats 1600000 in
/-- Stack-parameterized Stage 3 KEM seed unroll Part A (`+0x0b6c → +0x0c48`, draws `0..6`). -/
theorem kem_coins_a_placed_ok_at [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {st0 st : M.σ} {be : PreKeyBundleFields} {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)} {pqspkPtr secretsPtr : BitVec 64}
    {opkId : BitVec 32} {dh1 dh2 dh3 : SignalPqxdh.Bytes}
    {dh4? : Option SignalPqxdh.Bytes} {stk : Nat}
    {s0 s3 s : State} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (cfStk : Nat) (hcf_ext : extHookStack ≤ cfStk) (hcf_sub : cfStk ≤ stk - cliInitiateFrame)
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hCall : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 618)
      (withLsCodeRoLoaded lsmpl (coinsFillSpecPlacedW3 cfStk)))
    (hcoinsLt : x.coins.length < 2 ^ 63)
    (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hs3 : AtStage3Placed W X x be kp ekASk ekAPk pqspkPtr opkId s0 s3)
    (hctrl : InInitiatePlaced s0 s 0xb6c) (htr : s.trace = s0.trace)
    (hx20 : s.readReg64 (.gpr 20#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x348#64)
    (hx21 : s.readReg64 (.gpr 21#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x388#64)
    (hx22 : s.readReg64 (.gpr 22#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x408#64)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf)
    (hnext : ∀ (sa : State)
        (z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 : BitVec 32),
      let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
      let t := padCoins x.coins
      InInitiatePlaced s0 sa 0xc48 → sa.trace = s0.trace →
      sa.readReg64 (.gpr 20#5) = fsp + 0x348#64 →
      sa.readReg64 (.gpr 21#5) = fsp + 0x388#64 →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sa
        (S3InvPrefixPlaced A x s0 ∗ coinsCursorAtPlaced x.coinsP x.coins (32 + 4 * 7) ∗
          A.pool lim st sa ∗ stackAt fsp cfStk ∗
          memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
            (stk - cliInitiateFrame - cfStk) ∗
          A.live secretsPtr 192 1 ∗
          (secretsPtr ↦ₛ bytesToBv8 (dhPrefix dh1 dh2 dh3 dh4?)) ∗
          dhRemAt secretsPtr dh4? ∗
          memRegion fsp 8 ∗
          ((fsp + 0x68#64) ↦₃₂ coinWord t 0 (by decide)) ∗
          ((fsp + 0x60#64) ↦₃₂ coinWord t 1 (by decide)) ∗
          ((fsp + 0x5c#64) ↦₃₂ coinWord t 2 (by decide)) ∗
          ((fsp + 0x58#64) ↦₃₂ coinWord t 3 (by decide)) ∗
          ((fsp + 0x54#64) ↦₃₂ coinWord t 4 (by decide)) ∗
          ((fsp + 0x50#64) ↦₃₂ coinWord t 5 (by decide)) ∗
          ((fsp + 0x4c#64) ↦₃₂ z6) ∗ ((fsp + 0x48#64) ↦₃₂ z7) ∗
          ((fsp + 0x44#64) ↦₃₂ z8) ∗ ((fsp + 0x40#64) ↦₃₂ z9) ∗
          ((fsp + 0x3c#64) ↦₃₂ z10) ∗ ((fsp + 0x38#64) ↦₃₂ z11) ∗
          ((fsp + 0x34#64) ↦₃₂ z12) ∗ ((fsp + 0x30#64) ↦₃₂ z13) ∗
          ((fsp + 0x2c#64) ↦₃₂ z14) ∗ ((fsp + 0x28#64) ↦₃₂ z15) ∗
          ((fsp + 0x24#64) ↦₃₂ z16) ∗ ((fsp + 0x20#64) ↦₃₂ z17) ∗
          ((fsp + 0x1c#64) ↦₃₂ z18) ∗ ((fsp + 0x18#64) ↦₃₂ z19) ∗
          ((fsp + 0x14#64) ↦₃₂ z20) ∗ ((fsp + 0x10#64) ↦₃₂ z21) ∗
          ((fsp + 0x0c#64) ↦₃₂ z22) ∗ ((fsp + 0x08#64) ↦₃₂ z23) ∗
          memRegion (fsp + 0x64#64) 4 ∗ memRegion (fsp + 0x6c#64) 4 ∗
          ((fsp + 0x70#64) ↦₆₄ (fsp + 0x408#64)) ∗
          ((fsp + 0x78#64) ↦₆₄ (fsp + 0x3c8#64)) ∗
          stage3KeySlotsAt A.repAlloc fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
          memRegion (fsp + 0x930#64) 8 ∗ memRegion (fsp + 0x938#64) 0x20 ∗
          memRegion (fsp + 0x958#64) 0x48 ∗ ((fsp + 0x9a0#64) ↦ₛ ekASk) ∗
          ((fsp + 0x9c0#64) ↦ₛ x.bundle.kpk) ∗ memRegion (fsp + 0xfe0#64) 32 ∗
          memRegion (fsp + 0x1000#64) 0x600 ∗
          ((fsp + 0x1600#64) ↦₃₂ coinWord t 6 (by decide)) ∗
          memRegion (fsp + 0x1604#64) 20 ∗ memRegion (fsp + 0x1618#64) 0x648 ∗
          ((fsp + 0x1c60#64) ↦₆₄ 192#64) ∗ ((fsp + 0x1c68#64) ↦₆₄ secretsPtr) ∗
          ((fsp + 0x1c70#64) ↦₆₄ dhLenWord dh4?) ∗ memRegion (fsp + 0x1c78#64) 0x18)
        Q Qp oom) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s
      (S3InvPrefixPlaced A x s0 ∗ coinsCursorAtPlaced x.coinsP x.coins 32 ∗
        A.pool lim st s ∗ stackAt fsp extHookStack ∗
        memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
          (stk - cliInitiateFrame - extHookStack) ∗
        A.live secretsPtr 192 1 ∗
        (secretsPtr ↦ₛ bytesToBv8 (dhPrefix dh1 dh2 dh3 dh4?)) ∗
        dhRemAt secretsPtr dh4? ∗
        memRegion fsp 0x78 ∗ ((fsp + 0x78#64) ↦₆₄ (fsp + 0x3c8#64)) ∗
        stage3KeySlotsAt A.repAlloc fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
        memRegion (fsp + 0x930#64) 8 ∗ memRegion (fsp + 0x938#64) 0x20 ∗
        memRegion (fsp + 0x958#64) 0x48 ∗ ((fsp + 0x9a0#64) ↦ₛ ekASk) ∗
        memRegion (fsp + 0x9c0#64) 0xc40 ∗
        memRegion (fsp + 0x1600#64) 24 ∗ memRegion (fsp + 0x1618#64) 0x648 ∗
        ((fsp + 0x1c60#64) ↦₆₄ 192#64) ∗ ((fsp + 0x1c68#64) ↦₆₄ secretsPtr) ∗
        ((fsp + 0x1c70#64) ↦₆₄ dhLenWord dh4?) ∗ memRegion (fsp + 0x1c78#64) 0x18)
      Q Qp oom := by
  dsimp only
  set fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
  obtain ⟨_, _, hkpkLen, _, _, _, _, _⟩ := bundleEOf_props hs3.bundleEq
  have hsub_ext : extHookStack ≤ stk - cliInitiateFrame :=
    Nat.le_trans hcf_ext hcf_sub
  have hcf64 : cfStk ≤ 2 ^ 64 :=
    Nat.le_trans hcf_sub (stk_sub_le_2pow64 hstk64)
  have hstk_cf :
      stackAt fsp extHookStack ∗
        memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
          (stk - cliInitiateFrame - extHookStack) =
      stackAt fsp extHookStack ∗
        memRegion (fsp - BitVec.ofNat 64 cfStk)
          (cfStk - extHookStack) ∗
        memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
          (stk - cliInitiateFrame - cfStk) := by
    rw [sepConj_comm (stackAt fsp extHookStack),
        ← stackAt_sub_split_init fsp hsub_ext (stk_sub_le_2pow64 hstk64),
        stackAt_sub_split_init fsp hcf_sub (stk_sub_le_2pow64 hstk64),
        stackAt_sub_split_init fsp hcf_ext hcf64]
    sep_ac_rfl
  refine sepWPp_conseq_oom
    (P' := ((memRegion (fsp + 0x68#64) 4 ∗ memRegion (fsp + 0x60#64) 4 ∗
      memRegion (fsp + 0x5c#64) 4 ∗ memRegion (fsp + 0x58#64) 4 ∗ memRegion (fsp + 0x54#64) 4 ∗
      memRegion (fsp + 0x50#64) 4 ∗ memRegion (fsp + 0x4c#64) 4 ∗ memRegion (fsp + 0x48#64) 4 ∗
      memRegion (fsp + 0x44#64) 4 ∗ memRegion (fsp + 0x40#64) 4 ∗ memRegion (fsp + 0x3c#64) 4 ∗
      memRegion (fsp + 0x38#64) 4 ∗ memRegion (fsp + 0x34#64) 4 ∗ memRegion (fsp + 0x30#64) 4 ∗
      memRegion (fsp + 0x2c#64) 4 ∗ memRegion (fsp + 0x28#64) 4 ∗ memRegion (fsp + 0x24#64) 4 ∗
      memRegion (fsp + 0x20#64) 4 ∗ memRegion (fsp + 0x1c#64) 4 ∗ memRegion (fsp + 0x18#64) 4 ∗
      memRegion (fsp + 0x14#64) 4 ∗ memRegion (fsp + 0x10#64) 4 ∗ memRegion (fsp + 0x0c#64) 4 ∗
      memRegion (fsp + 0x08#64) 4 ∗
      memRegion (fsp + 0x70#64) 8 ∗ memRegion (fsp + 0x1600#64) 4 ∗ emp) ∗
     (S3InvPrefixPlaced A x s0 ∗ coinsCursorAtPlaced x.coinsP x.coins 32 ∗
      A.pool lim st s ∗ stackAt fsp extHookStack ∗
      memRegion (fsp - BitVec.ofNat 64 cfStk) (cfStk - extHookStack) ∗
      memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
        (stk - cliInitiateFrame - cfStk) ∗
      A.live secretsPtr 192 1 ∗
      (secretsPtr ↦ₛ bytesToBv8 (dhPrefix dh1 dh2 dh3 dh4?)) ∗
      dhRemAt secretsPtr dh4? ∗
      memRegion fsp 8 ∗
      memRegion (fsp + 0x64#64) 4 ∗ memRegion (fsp + 0x6c#64) 4 ∗
      ((fsp + 0x78#64) ↦₆₄ (fsp + 0x3c8#64)) ∗
      stage3KeySlotsAt A.repAlloc fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
      memRegion (fsp + 0x930#64) 8 ∗ memRegion (fsp + 0x938#64) 0x20 ∗
      memRegion (fsp + 0x958#64) 0x48 ∗ ((fsp + 0x9a0#64) ↦ₛ ekASk) ∗
      memRegion (fsp + 0x9c0#64) 1568 ∗ memRegion (fsp + 0xfe0#64) 32 ∗
      memRegion (fsp + 0x1000#64) 0x600 ∗ memRegion (fsp + 0x1604#64) 20 ∗
      memRegion (fsp + 0x1618#64) 0x648 ∗
      ((fsp + 0x1c60#64) ↦₆₄ 192#64) ∗ ((fsp + 0x1c68#64) ↦₆₄ secretsPtr) ∗
      ((fsp + 0x1c70#64) ↦₆₄ dhLenWord dh4?) ∗ memRegion (fsp + 0x1c78#64) 0x18)))
    (by
      dsimp only [fsp] at hstk_cf ⊢
      refine sep_replace (Entails.of_eq hstk_cf) (by sep_frame) ?_
      rw [kem_locals_9c0, kem_locals_1600, scratch120_split]
      sep_frame) ?_
  refine mem4_elim_word fun z0 => mem4_elim_word fun z1 =>
    mem4_elim_word fun z2 => mem4_elim_word fun z3 =>
    mem4_elim_word fun z4 => mem4_elim_word fun z5 =>
    mem4_elim_word fun z6 => mem4_elim_word fun z7 =>
    mem4_elim_word fun z8 => mem4_elim_word fun z9 =>
    mem4_elim_word fun z10 => mem4_elim_word fun z11 =>
    mem4_elim_word fun z12 => mem4_elim_word fun z13 =>
    mem4_elim_word fun z14 => mem4_elim_word fun z15 =>
    mem4_elim_word fun z16 => mem4_elim_word fun z17 =>
    mem4_elim_word fun z18 => mem4_elim_word fun z19 =>
    mem4_elim_word fun z20 => mem4_elim_word fun z21 =>
    mem4_elim_word fun z22 => mem4_elim_word fun z23 =>
    mem8_elim_word fun z70 => mem4_elim_word fun z1600 => ?_
  rw [emp_sepConj]
  obtain ⟨halign_b, _, hfsp_b⟩ := hctrl.step_ctx fsp
  refine sepWPp_conseq_oom
    (show _ ⊢ ((fsp + 0x70#64) ↦₆₄ z70) ∗ ((fsp + 0x428#64) ↦₆₄ pqspkPtr) ∗
        ((fsp + 0x430#64) ↦₆₄ 1568#64) ∗ _ by
      dsimp only [fsp, stage3KeySlotsAt]; sep_frame) ?_
  refine' s3_block_to_call_vm_placed hh (lsρ memcpyName)
    0xb8c (Φ := fun sm =>
      sm.readReg64 .x0 = fsp + 0x9c0#64 ∧ sm.readReg64 .x1 = pqspkPtr ∧
      sm.readReg64 .x2 = 1568#64 ∧
      sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧
      sm.readReg64 (.gpr 21#5) = fsp + 0x388#64)
    hctrl ?_ ?_; rotate_left 1
  · have hpc : s.pc = (blkPl_521).base + BitVec.ofNat 64 0xb6c := hctrl.pc
    rw [hfsp_b]
    exact s3_step_b6c_b8c_placed pqspkPtr z70 _ halign_b hpc hctrl.run
      (by rwa [← hfsp_b]) (by rwa [← hfsp_b]) (by rwa [← hfsp_b])
  · intro sm_mc hvm_mc hctrl_mc hpcm_mc hlrm_mc htrm_mc
      ⟨hx0_mc, hx1_mc, hx2_mc, hx20_mc, hx21_mc⟩
    have hpool_mc : A.pool lim st s = A.pool lim st sm_mc :=
      (A.pool_transport lim st s sm_mc hvm_mc).symm
    rw [← hfsp_b] at *
    refine s3_memcpy_pool_placed hh (fsp + 0x9c0#64) pqspkPtr x.bundle.kpk st _
      hctrl_mc (htrm_mc.trans htr) hpcm_mc hlrm_mc
      hx0_mc hx1_mc (by rw [hx2_mc, hkpkLen]; decide) hpanic
      (by rw [hpool_mc, hctrl_mc.sp, hkpkLen]; (try dsimp only [fsp]); sep_frame) ?_
    intro s_0 hctrl_0 hcs_0 _ htr_0
    rw [hctrl_mc.sp]
    have hx20_0 := hcs_0.2.1.trans hx20_mc; have hx21_0 := hcs_0.2.2.1.trans hx21_mc
    have hcf_re :
        stackAt fsp extHookStack ∗
          memRegion (fsp - BitVec.ofNat 64 cfStk)
            (cfStk - extHookStack) =
        stackAt fsp cfStk := by
      rw [sepConj_comm, ← stackAt_sub_split_init fsp hcf_ext hcf64]
    refine sepWPp_conseq_oom
      (sep_replace (sepConj_mono
        (Entails.of_eq (s3_repack_kpk (R := A.repAlloc) fsp x kp ekASk ekAPk pqspkPtr opkId))
        (Entails.of_eq hcf_re))
        (by cases x.bundle.opk <;> ((try dsimp only [fsp]); sep_frame)) (Entails.refl _)) ?_
    obtain ⟨halign_0, _, hfsp_0⟩ := hctrl_0.step_ctx fsp
    refine sepWPp_conseq_oom
      (show _ ⊢ ((fsp + 0x1600#64) ↦₃₂ z1600) ∗ _ by dsimp only [fsp]; sep_frame) ?_
    refine' s3_block_to_call_vm_placed hh (lsmpl.base 618)
      0xba0 (Φ := fun sm =>
        sm.readReg64 .x0 = fsp + 0x1600#64 ∧ sm.readReg64 .x1 = 4#64 ∧
        sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧
        sm.readReg64 (.gpr 21#5) = fsp + 0x388#64)
      hctrl_0 ?_ ?_; rotate_left 1
    · have hpc : s_0.pc = (blkPl_521).base + BitVec.ofNat 64 0xb8c := hctrl_0.pc
      rw [hfsp_0]
      exact s3_step_b8c_ba0_placed z1600 _ halign_0 hpc hctrl_0.run
        (by rwa [← hfsp_0]) (by rwa [← hfsp_0])
    · intro sm_d0 hvm_d0 hctrl_d0 hpcm_d0 hlrm_d0 htrm_d0 ⟨hx0_d0, hx1_d0, hx20_d0, hx21_d0⟩
      have hpool_d0 : A.pool lim st s_0 = A.pool lim st sm_d0 :=
        (A.pool_transport lim st s_0 sm_d0 hvm_d0).symm
      rw [← hfsp_0] at *
      refine s3_coins_fill4_pool_at cfStk hh hCall hcoinsLt 0 (by decide) st _
        hctrl_d0 (htrm_d0.trans (htr_0.trans (htrm_mc.trans htr))) hpcm_d0 hlrm_d0
        hx0_d0 hx1_d0 hpanic
        (by rw [hpool_d0, hctrl_d0.sp]; (try dsimp only [fsp]); simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]; sep_frame) ?_
      intro s_1 hctrl_1 hcs_1 htr_1
      rw [hctrl_d0.sp]
      have htr1 : s_1.trace = s0.trace :=
        htr_1.trans (htrm_d0.trans (htr_0.trans (htrm_mc.trans htr)))
      have hx20_1 := hcs_1.2.1.trans hx20_d0; have hx21_1 := hcs_1.2.2.1.trans hx21_d0
      refine s3_draw_pool_at cfStk hh hCall hcoinsLt 1 (by decide) (by decide)
        0xba0 0xbbc 0x68#64 z0 st _ hctrl_1 htr1 hx20_1 hx21_1 hpanic
        (by intro G halign hpc hrun hx20' hx21'
            dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521, BitVec.ofNat_eq_ofNat] at hpc ⊢
            try simp only [arm64_norm, wp_norm] at hx20' hx21'
            by_vm_steps (
              wp_steps
              exact s3_done_call_vm (by wp_norm_lhs)
                (by simp only [arm64_norm, wp_norm]; sep_frame)
                ⟨by wp_norm_goal, by wp_norm_goal,
                 by simp only [hx20', arm64_norm, wp_norm],
                 by simp only [hx21', arm64_norm, wp_norm]⟩
                (hpc := by (try wp_norm_goal); try (clear * -; bv_omega))
                (hlr := by (try wp_norm_goal); try (clear * -; bv_omega))))
        (by (try dsimp only [fsp]); simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]; sep_frame)
        fun s_2 hctrl_2 htr2 hx20_2 hx21_2 => ?_
      refine s3_draw_pool_at cfStk hh hCall hcoinsLt 2 (by decide) (by decide)
        0xbbc 0xbd8 0x60#64 z1 st _ hctrl_2 htr2 hx20_2 hx21_2 hpanic
        (by intro G halign hpc hrun hx20' hx21'
            dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521, BitVec.ofNat_eq_ofNat] at hpc ⊢
            try simp only [arm64_norm, wp_norm] at hx20' hx21'
            by_vm_steps (
              wp_steps
              exact s3_done_call_vm (by wp_norm_lhs)
                (by simp only [arm64_norm, wp_norm]; sep_frame)
                ⟨by wp_norm_goal, by wp_norm_goal,
                 by simp only [hx20', arm64_norm, wp_norm],
                 by simp only [hx21', arm64_norm, wp_norm]⟩
                (hpc := by (try wp_norm_goal); try (clear * -; bv_omega))
                (hlr := by (try wp_norm_goal); try (clear * -; bv_omega))))
        (by (try dsimp only [fsp]); simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]; sep_frame)
        fun s_3 hctrl_3 htr3 hx20_3 hx21_3 => ?_
      refine s3_draw_pool_at cfStk hh hCall hcoinsLt 3 (by decide) (by decide)
        0xbd8 0xbf4 0x5c#64 z2 st _ hctrl_3 htr3 hx20_3 hx21_3 hpanic
        (by intro G halign hpc hrun hx20' hx21'
            dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521, BitVec.ofNat_eq_ofNat] at hpc ⊢
            try simp only [arm64_norm, wp_norm] at hx20' hx21'
            by_vm_steps (
              wp_steps
              exact s3_done_call_vm (by wp_norm_lhs)
                (by simp only [arm64_norm, wp_norm]; sep_frame)
                ⟨by wp_norm_goal, by wp_norm_goal,
                 by simp only [hx20', arm64_norm, wp_norm],
                 by simp only [hx21', arm64_norm, wp_norm]⟩
                (hpc := by (try wp_norm_goal); try (clear * -; bv_omega))
                (hlr := by (try wp_norm_goal); try (clear * -; bv_omega))))
        (by (try dsimp only [fsp]); simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]; sep_frame)
        fun s_4 hctrl_4 htr4 hx20_4 hx21_4 => ?_
      refine s3_draw_pool_at cfStk hh hCall hcoinsLt 4 (by decide) (by decide)
        0xbf4 0xc10 0x58#64 z3 st _ hctrl_4 htr4 hx20_4 hx21_4 hpanic
        (by intro G halign hpc hrun hx20' hx21'
            dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521, BitVec.ofNat_eq_ofNat] at hpc ⊢
            try simp only [arm64_norm, wp_norm] at hx20' hx21'
            by_vm_steps (
              wp_steps
              exact s3_done_call_vm (by wp_norm_lhs)
                (by simp only [arm64_norm, wp_norm]; sep_frame)
                ⟨by wp_norm_goal, by wp_norm_goal,
                 by simp only [hx20', arm64_norm, wp_norm],
                 by simp only [hx21', arm64_norm, wp_norm]⟩
                (hpc := by (try wp_norm_goal); try (clear * -; bv_omega))
                (hlr := by (try wp_norm_goal); try (clear * -; bv_omega))))
        (by (try dsimp only [fsp]); simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]; sep_frame)
        fun s_5 hctrl_5 htr5 hx20_5 hx21_5 => ?_
      refine s3_draw_pool_at cfStk hh hCall hcoinsLt 5 (by decide) (by decide)
        0xc10 0xc2c 0x54#64 z4 st _ hctrl_5 htr5 hx20_5 hx21_5 hpanic
        (by intro G halign hpc hrun hx20' hx21'
            dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521, BitVec.ofNat_eq_ofNat] at hpc ⊢
            try simp only [arm64_norm, wp_norm] at hx20' hx21'
            by_vm_steps (
              wp_steps
              exact s3_done_call_vm (by wp_norm_lhs)
                (by simp only [arm64_norm, wp_norm]; sep_frame)
                ⟨by wp_norm_goal, by wp_norm_goal,
                 by simp only [hx20', arm64_norm, wp_norm],
                 by simp only [hx21', arm64_norm, wp_norm]⟩
                (hpc := by (try wp_norm_goal); try (clear * -; bv_omega))
                (hlr := by (try wp_norm_goal); try (clear * -; bv_omega))))
        (by (try dsimp only [fsp]); simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]; sep_frame)
        fun s_6 hctrl_6 htr6 hx20_6 hx21_6 => ?_
      refine s3_draw_pool_at cfStk hh hCall hcoinsLt 6 (by decide) (by decide)
        0xc2c 0xc48 0x50#64 z5 st _ hctrl_6 htr6 hx20_6 hx21_6 hpanic
        (by intro G halign hpc hrun hx20' hx21'
            dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521, BitVec.ofNat_eq_ofNat] at hpc ⊢
            try simp only [arm64_norm, wp_norm] at hx20' hx21'
            by_vm_steps (
              wp_steps
              exact s3_done_call_vm (by wp_norm_lhs)
                (by simp only [arm64_norm, wp_norm]; sep_frame)
                ⟨by wp_norm_goal, by wp_norm_goal,
                 by simp only [hx20', arm64_norm, wp_norm],
                 by simp only [hx21', arm64_norm, wp_norm]⟩
                (hpc := by (try wp_norm_goal); try (clear * -; bv_omega))
                (hlr := by (try wp_norm_goal); try (clear * -; bv_omega))))
        (by (try dsimp only [fsp]); simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]; sep_frame)
        fun s_7 hctrl_7 htr7 hx20_7 hx21_7 => ?_
      exact sepWPp_conseq_oom
        (by (try dsimp only [fsp]); simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]; sep_frame)
        (hnext s_7 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23
          hctrl_7 htr7 hx20_7 hx21_7)

theorem kem_coins_a_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {st0 st : M.σ} {be : PreKeyBundleFields} {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)} {pqspkPtr secretsPtr : BitVec 64}
    {opkId : BitVec 32} {dh1 dh2 dh3 : SignalPqxdh.Bytes}
    {dh4? : Option SignalPqxdh.Bytes} {stk : Nat}
    {s0 s3 s : State} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hCoins : ∀ {cStk : Nat}, cliCoinsFillStack ≤ cStk → cStk ≤ 2 ^ 63 →
      subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 618)
        (withLsCodeRoLoaded lsmpl (coinsFillSpecPlacedW3 cStk)))
    (hcoinsLt : x.coins.length < 2 ^ 63)
    (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hs3 : AtStage3Placed W X x be kp ekASk ekAPk pqspkPtr opkId s0 s3)
    (hctrl : InInitiatePlaced s0 s 0xb6c) (htr : s.trace = s0.trace)
    (hx20 : s.readReg64 (.gpr 20#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x348#64)
    (hx21 : s.readReg64 (.gpr 21#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x388#64)
    (hx22 : s.readReg64 (.gpr 22#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x408#64)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf)
    (hnext : ∀ (sa : State)
        (z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 : BitVec 32),
      let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
      let t := padCoins x.coins
      InInitiatePlaced s0 sa 0xc48 → sa.trace = s0.trace →
      sa.readReg64 (.gpr 20#5) = fsp + 0x348#64 →
      sa.readReg64 (.gpr 21#5) = fsp + 0x388#64 →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sa
        (S3InvPrefixPlaced A x s0 ∗ coinsCursorAtPlaced x.coinsP x.coins (32 + 4 * 7) ∗
          A.pool lim st sa ∗ stackAt fsp cliCoinsFillStack ∗
          memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
            (stk - cliInitiateFrame - cliCoinsFillStack) ∗
          A.live secretsPtr 192 1 ∗
          (secretsPtr ↦ₛ bytesToBv8 (dhPrefix dh1 dh2 dh3 dh4?)) ∗
          dhRemAt secretsPtr dh4? ∗
          memRegion fsp 8 ∗
          ((fsp + 0x68#64) ↦₃₂ coinWord t 0 (by decide)) ∗
          ((fsp + 0x60#64) ↦₃₂ coinWord t 1 (by decide)) ∗
          ((fsp + 0x5c#64) ↦₃₂ coinWord t 2 (by decide)) ∗
          ((fsp + 0x58#64) ↦₃₂ coinWord t 3 (by decide)) ∗
          ((fsp + 0x54#64) ↦₃₂ coinWord t 4 (by decide)) ∗
          ((fsp + 0x50#64) ↦₃₂ coinWord t 5 (by decide)) ∗
          ((fsp + 0x4c#64) ↦₃₂ z6) ∗ ((fsp + 0x48#64) ↦₃₂ z7) ∗
          ((fsp + 0x44#64) ↦₃₂ z8) ∗ ((fsp + 0x40#64) ↦₃₂ z9) ∗
          ((fsp + 0x3c#64) ↦₃₂ z10) ∗ ((fsp + 0x38#64) ↦₃₂ z11) ∗
          ((fsp + 0x34#64) ↦₃₂ z12) ∗ ((fsp + 0x30#64) ↦₃₂ z13) ∗
          ((fsp + 0x2c#64) ↦₃₂ z14) ∗ ((fsp + 0x28#64) ↦₃₂ z15) ∗
          ((fsp + 0x24#64) ↦₃₂ z16) ∗ ((fsp + 0x20#64) ↦₃₂ z17) ∗
          ((fsp + 0x1c#64) ↦₃₂ z18) ∗ ((fsp + 0x18#64) ↦₃₂ z19) ∗
          ((fsp + 0x14#64) ↦₃₂ z20) ∗ ((fsp + 0x10#64) ↦₃₂ z21) ∗
          ((fsp + 0x0c#64) ↦₃₂ z22) ∗ ((fsp + 0x08#64) ↦₃₂ z23) ∗
          memRegion (fsp + 0x64#64) 4 ∗ memRegion (fsp + 0x6c#64) 4 ∗
          ((fsp + 0x70#64) ↦₆₄ (fsp + 0x408#64)) ∗
          ((fsp + 0x78#64) ↦₆₄ (fsp + 0x3c8#64)) ∗
          stage3KeySlotsAt A.repAlloc fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
          memRegion (fsp + 0x930#64) 8 ∗ memRegion (fsp + 0x938#64) 0x20 ∗
          memRegion (fsp + 0x958#64) 0x48 ∗ ((fsp + 0x9a0#64) ↦ₛ ekASk) ∗
          ((fsp + 0x9c0#64) ↦ₛ x.bundle.kpk) ∗ memRegion (fsp + 0xfe0#64) 32 ∗
          memRegion (fsp + 0x1000#64) 0x600 ∗
          ((fsp + 0x1600#64) ↦₃₂ coinWord t 6 (by decide)) ∗
          memRegion (fsp + 0x1604#64) 20 ∗ memRegion (fsp + 0x1618#64) 0x648 ∗
          ((fsp + 0x1c60#64) ↦₆₄ 192#64) ∗ ((fsp + 0x1c68#64) ↦₆₄ secretsPtr) ∗
          ((fsp + 0x1c70#64) ↦₆₄ dhLenWord dh4?) ∗ memRegion (fsp + 0x1c78#64) 0x18)
        Q Qp oom) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s
      (S3InvPrefixPlaced A x s0 ∗ coinsCursorAtPlaced x.coinsP x.coins 32 ∗
        A.pool lim st s ∗ stackAt fsp extHookStack ∗
        memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
          (stk - cliInitiateFrame - extHookStack) ∗
        A.live secretsPtr 192 1 ∗
        (secretsPtr ↦ₛ bytesToBv8 (dhPrefix dh1 dh2 dh3 dh4?)) ∗
        dhRemAt secretsPtr dh4? ∗
        memRegion fsp 0x78 ∗ ((fsp + 0x78#64) ↦₆₄ (fsp + 0x3c8#64)) ∗
        stage3KeySlotsAt A.repAlloc fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
        memRegion (fsp + 0x930#64) 8 ∗ memRegion (fsp + 0x938#64) 0x20 ∗
        memRegion (fsp + 0x958#64) 0x48 ∗ ((fsp + 0x9a0#64) ↦ₛ ekASk) ∗
        memRegion (fsp + 0x9c0#64) 0xc40 ∗
        memRegion (fsp + 0x1600#64) 24 ∗ memRegion (fsp + 0x1618#64) 0x648 ∗
        ((fsp + 0x1c60#64) ↦₆₄ 192#64) ∗ ((fsp + 0x1c68#64) ↦₆₄ secretsPtr) ∗
        ((fsp + 0x1c70#64) ↦₆₄ dhLenWord dh4?) ∗ memRegion (fsp + 0x1c78#64) 0x18)
      Q Qp oom :=
  kem_coins_a_placed_ok_at cliCoinsFillStack (by decide)
    (Nat.le_trans (by decide) (stk_sub_ge_base hstk)) hh
    (hCoins (le_refl cliCoinsFillStack) (by decide))
    hcoinsLt hstk hstk64 hs3 hctrl htr hx20 hx21 hx22 hpanic hnext

theorem kem_coins_a_hooks_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {st0 st : M.σ} {be : PreKeyBundleFields} {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)} {pqspkPtr secretsPtr : BitVec 64}
    {opkId : BitVec 32} {dh1 dh2 dh3 : SignalPqxdh.Bytes}
    {dh4? : Option SignalPqxdh.Bytes} {stk : Nat}
    {s0 s3 s : State} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hcoinsLt : x.coins.length < 2 ^ 63)
    (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hs3 : AtStage3Placed W X x be kp ekASk ekAPk pqspkPtr opkId s0 s3)
    (hctrl : InInitiatePlaced s0 s 0xb6c) (htr : s.trace = s0.trace)
    (hx20 : s.readReg64 (.gpr 20#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x348#64)
    (hx21 : s.readReg64 (.gpr 21#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x388#64)
    (hx22 : s.readReg64 (.gpr 22#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x408#64)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf)
    (hnext : ∀ (sa : State)
        (z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 : BitVec 32),
      let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
      let t := padCoins x.coins
      InInitiatePlaced s0 sa 0xc48 → sa.trace = s0.trace →
      sa.readReg64 (.gpr 20#5) = fsp + 0x348#64 →
      sa.readReg64 (.gpr 21#5) = fsp + 0x388#64 →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sa
        (S3InvPrefixPlaced A x s0 ∗ coinsCursorAtPlaced x.coinsP x.coins (32 + 4 * 7) ∗
          A.pool lim st sa ∗ stackAt fsp cliCoinsFillStackPlaced ∗
          memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
            (stk - cliInitiateFrame - cliCoinsFillStackPlaced) ∗
          A.live secretsPtr 192 1 ∗
          (secretsPtr ↦ₛ bytesToBv8 (dhPrefix dh1 dh2 dh3 dh4?)) ∗
          dhRemAt secretsPtr dh4? ∗
          memRegion fsp 8 ∗
          ((fsp + 0x68#64) ↦₃₂ coinWord t 0 (by decide)) ∗
          ((fsp + 0x60#64) ↦₃₂ coinWord t 1 (by decide)) ∗
          ((fsp + 0x5c#64) ↦₃₂ coinWord t 2 (by decide)) ∗
          ((fsp + 0x58#64) ↦₃₂ coinWord t 3 (by decide)) ∗
          ((fsp + 0x54#64) ↦₃₂ coinWord t 4 (by decide)) ∗
          ((fsp + 0x50#64) ↦₃₂ coinWord t 5 (by decide)) ∗
          ((fsp + 0x4c#64) ↦₃₂ z6) ∗ ((fsp + 0x48#64) ↦₃₂ z7) ∗
          ((fsp + 0x44#64) ↦₃₂ z8) ∗ ((fsp + 0x40#64) ↦₃₂ z9) ∗
          ((fsp + 0x3c#64) ↦₃₂ z10) ∗ ((fsp + 0x38#64) ↦₃₂ z11) ∗
          ((fsp + 0x34#64) ↦₃₂ z12) ∗ ((fsp + 0x30#64) ↦₃₂ z13) ∗
          ((fsp + 0x2c#64) ↦₃₂ z14) ∗ ((fsp + 0x28#64) ↦₃₂ z15) ∗
          ((fsp + 0x24#64) ↦₃₂ z16) ∗ ((fsp + 0x20#64) ↦₃₂ z17) ∗
          ((fsp + 0x1c#64) ↦₃₂ z18) ∗ ((fsp + 0x18#64) ↦₃₂ z19) ∗
          ((fsp + 0x14#64) ↦₃₂ z20) ∗ ((fsp + 0x10#64) ↦₃₂ z21) ∗
          ((fsp + 0x0c#64) ↦₃₂ z22) ∗ ((fsp + 0x08#64) ↦₃₂ z23) ∗
          memRegion (fsp + 0x64#64) 4 ∗ memRegion (fsp + 0x6c#64) 4 ∗
          ((fsp + 0x70#64) ↦₆₄ (fsp + 0x408#64)) ∗
          ((fsp + 0x78#64) ↦₆₄ (fsp + 0x3c8#64)) ∗
          stage3KeySlotsAt A.repAlloc fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
          memRegion (fsp + 0x930#64) 8 ∗ memRegion (fsp + 0x938#64) 0x20 ∗
          memRegion (fsp + 0x958#64) 0x48 ∗ ((fsp + 0x9a0#64) ↦ₛ ekASk) ∗
          ((fsp + 0x9c0#64) ↦ₛ x.bundle.kpk) ∗ memRegion (fsp + 0xfe0#64) 32 ∗
          memRegion (fsp + 0x1000#64) 0x600 ∗
          ((fsp + 0x1600#64) ↦₃₂ coinWord t 6 (by decide)) ∗
          memRegion (fsp + 0x1604#64) 20 ∗ memRegion (fsp + 0x1618#64) 0x648 ∗
          ((fsp + 0x1c60#64) ↦₆₄ 192#64) ∗ ((fsp + 0x1c68#64) ↦₆₄ secretsPtr) ∗
          ((fsp + 0x1c70#64) ↦₆₄ dhLenWord dh4?) ∗ memRegion (fsp + 0x1c78#64) 0x18)
        Q Qp oom) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s
      (S3InvPrefixPlaced A x s0 ∗ coinsCursorAtPlaced x.coinsP x.coins 32 ∗
        A.pool lim st s ∗ stackAt fsp extHookStack ∗
        memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
          (stk - cliInitiateFrame - extHookStack) ∗
        A.live secretsPtr 192 1 ∗
        (secretsPtr ↦ₛ bytesToBv8 (dhPrefix dh1 dh2 dh3 dh4?)) ∗
        dhRemAt secretsPtr dh4? ∗
        memRegion fsp 0x78 ∗ ((fsp + 0x78#64) ↦₆₄ (fsp + 0x3c8#64)) ∗
        stage3KeySlotsAt A.repAlloc fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
        memRegion (fsp + 0x930#64) 8 ∗ memRegion (fsp + 0x938#64) 0x20 ∗
        memRegion (fsp + 0x958#64) 0x48 ∗ ((fsp + 0x9a0#64) ↦ₛ ekASk) ∗
        memRegion (fsp + 0x9c0#64) 0xc40 ∗
        memRegion (fsp + 0x1600#64) 24 ∗ memRegion (fsp + 0x1618#64) 0x648 ∗
        ((fsp + 0x1c60#64) ↦₆₄ 192#64) ∗ ((fsp + 0x1c68#64) ↦₆₄ secretsPtr) ∗
        ((fsp + 0x1c70#64) ↦₆₄ dhLenWord dh4?) ∗ memRegion (fsp + 0x1c78#64) 0x18)
      Q Qp oom :=
  kem_coins_a_placed_ok_at cliCoinsFillStackPlaced (by decide)
    (Nat.le_trans (by decide) (stk_sub_ge_base hstk)) hh
    (coinsFill_cli_placed_ok hh (le_refl cliCoinsFillStackPlaced) (by decide))
    hcoinsLt hstk hstk64 hs3 hctrl htr hx20 hx21 hx22 hpanic hnext

end

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.KemCoinsAPlacedBudget
