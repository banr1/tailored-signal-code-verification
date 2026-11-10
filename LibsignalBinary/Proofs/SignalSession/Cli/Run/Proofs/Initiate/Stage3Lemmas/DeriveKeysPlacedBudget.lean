/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.DeriveKeysAPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.DeriveKeysNonePlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.DeriveKeysPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.DhStepsAPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.DhStepsB2PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.DhStepsBPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.DhStepsCPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.KemCoinsAPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.KemCoinsBPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.KemCoinsCPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.KemEncapsPlacedBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Budget-Threaded Stage 3 `HandshakeKeys::derive` and Full Composition (`[LibsignalPlacement]`)

Verifies `<HandshakeKeys>::derive` (`+0x1044 → +0x10a4`, general `dh4?`) and composes the full
Stage 3 PQXDH + KEM pipeline (`+0x0760 → +0x10a4` and zero-DH unwind exits) under
`RustCliAllocBudget M`.
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
open CryptoVerification.E2E
  (PreKeyBundleFields UnreachedPqxdhPrimitives initiateInput initiateKemCoins modelPrims toU8 vecU8)
open CryptoVerification.E2E.Pqxdh.Initiator
  (F_X25519 buildSecrets bytesToBv8 e2e_vecU8_length pqxdhEntryStack)
open CryptoVerification.E2E.Pqxdh.ResponderCore
  (and_ff32_hi56_3 and_ff_hi56_3 bytesToBv8_length extractLsb_hi56_3 ofSignalPqxdhPrimitives
   zext64_trunc32_hi56_3_and_ff)
open CryptoVerification.LibsignalPublicApi.StoreKit (withLsCodeRoLoaded)
open CryptoVerification.LibsignalSpqrV1 (Params)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.RecordCodecs (IdentityKeyPair)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced lsRustDeallocSymCli)
open CryptoVerification.SignalSession.Cli.RunCompose (InitGhost RunSem)
open CryptoVerification.SignalSession.Cli.RunProofs
  (cliInitiateFrame cliInitiateNeed initDef padCoins)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate
  (AtStage3Placed AtStage4Placed InInitiatePlaced cliCoinsFillStack coinsCursorAtPlaced
   initEntryPlaced initPcPlaced initProgPlaced stage3KeySlotsAt stk_sub_ge_base)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage3Lemmas
  (append_bv8_at buildSecrets_take32_eq bundleEOf_props bytes32_exists_cells4 bytesToBv8_toU8_eq
   cells4_to_memRegion32 dh4_some_eq dhLenWord dhPrefix dhRemAt lay32 lay192 memRegion32_cells4
   memRegion_merge_at modelPrims_x25519_len pointsToBytes_entails_memRegion_len sepWPp_conseq_oom
   sepWPp_exists_elim_oom sepWPp_pure_elim_oom sep_replace stackAt_sub_split_init
   stage4_keysOk_of_parts tail_locals_collapse)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.DeriveKeysPlacedBudget

noncomputable section

open Arm64 Arm64.Obj Arm64.Process ProofLib SepProp
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEvents RustCliAllocBudget fitsEvents_append
   rustAllocEvents rustDeallocEvents)
open LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.HandshakeDeriveBudget
  (handshakeKeysDerivePlacedBaseSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.CoinsFillPlacedBudget
  (coinsFillSpecPlacedW3)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.DefsPlacedBudget
  (InitExitPostPlaced InitPanicPostPlaced stage3MemPlaced stage4MemPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlacedBudget
  (RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.LocalCalleesPlacedBudget
  (InitLocalCalleesPlaced SubsetA4InitCalleesPlaced handshakeDerive_cli_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.CollapsePlacedBudget
  (s3_block_to_call_vm_placed s3_dealloc_stack_placed s3_done_call_vm)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.DefsPlacedBudget
  (s3_call_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.DeriveKeysAPlacedBudget
  (deriveKeysAAllocPrefixEvents deriveKeysAEvents derive_keys_a_hooks_placed_ok
   derive_keys_a_placed_ok fitsEvents_deriveKeysAAllocPrefix_of_full)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.DeriveKeysNonePlacedBudget
  (deriveKeysNoneEvents derive_keys_none_of_ok stepEvents_deriveKeysNoneEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.DhHelpersPlacedBudget
  (S3InvPrefixPlaced fitsEvents_s3CalcAgreeEvents_of_alloc32 s3CalcAgreeEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.DhStepsAPlacedBudget
  (dh1OkEvents dh1UnwindEvents dh1_step_hooks_placed_ok dh1_step_placed_ok fitsEvents_dh1_of_okEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.DhStepsB2PlacedBudget
  (dh3StepOkEvents dh3_step_hooks_placed_ok dh3_step_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.DhStepsBPlacedBudget
  (dh2OkEvents dh2_step_hooks_placed_ok dh2_step_placed_ok fitsEvents_dh2_of_okEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.DhStepsCPlacedBudget
  (dh4OptEvents dh4_step_hooks_placed_ok dh4_step_placed_ok s3Dh4CalcAgreeEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.EarlyExitPlacedBudget
  (stepEvents_unwind1548Events unwind1548Events)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.KemCoinsAPlacedBudget
  (kem_coins_a_hooks_placed_ok kem_coins_a_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.KemCoinsBPlacedBudget
  (kem_coins_b_hooks_placed_ok kem_coins_b_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.KemCoinsCPlacedBudget
  (kem_coins_c_hooks_placed_ok kem_coins_c_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.KemEncapsPlacedBudget
  (kem_encaps_hooks_placed_ok kem_encaps_placed_ok)
open Arm64.Obj (MultiPlacement)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate (initProgExtPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (CliGhostHooks cliGhostExterns)

attribute [local irreducible] Program.fetch Program.externAt? S3InvPrefixPlaced coinsCursorAtPlaced
attribute [local simp, local arm64_norm, local wp_norm]
  extractLsb_hi56_3 and_ff_hi56_3 and_ff32_hi56_3 zext64_trunc32_hi56_3_and_ff

/-! ## `AllocEvent` Sequences & `FitsEvents` Decomposition -/

/-- Allocator events emitted across `+0x1044 → +0x10a4` (`<HandshakeKeys>::derive`). -/
abbrev deriveKeysEvents : List AllocEvent :=
  deriveKeysNoneEvents

theorem stepEvents_deriveKeysEvents (M : AllocCostModel) (st : M.σ) :
    M.stepEvents (rustDeallocEvents 192 1) (M.stepEvents (rustDeallocEvents 32 1) st) =
      M.stepEvents deriveKeysEvents st :=
  stepEvents_deriveKeysNoneEvents M st

/-- Model-level optional `DH4` shared secret computed by `initiateInput`. -/
def stage3Dh4Opt (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (kp : IdentityKeyPair) (be : PreKeyBundleFields) (coins : List (BitVec 8)) :
    Option SignalPqxdh.Bytes :=
  ((initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins coins)).bundle.opkB?.map
    fun (_, opkPk) =>
      (modelPrims X ⟨W.C, W.Q⟩).x25519
        (initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins coins)).ekASk
        opkPk)

abbrev stage3Dh1UnwindEvents : List AllocEvent :=
  dh1UnwindEvents

def stage3AfterDh1Events : List AllocEvent :=
  dh1OkEvents

def stage3Dh2UnwindEvents : List AllocEvent :=
  stage3AfterDh1Events ++ unwind1548Events

def stage3AfterDh2Events : List AllocEvent :=
  stage3AfterDh1Events ++ dh2OkEvents

def stage3Dh3UnwindEvents : List AllocEvent :=
  stage3AfterDh2Events ++ unwind1548Events

def stage3AfterDh3Events : List AllocEvent :=
  stage3AfterDh2Events ++ dh3StepOkEvents

def stage3Dh4UnwindEvents : List AllocEvent :=
  stage3AfterDh3Events ++ unwind1548Events

def stage3AfterDh4Events (dh4? : Option SignalPqxdh.Bytes) : List AllocEvent :=
  stage3AfterDh3Events ++ dh4OptEvents dh4?

def stage3AfterKemBoxEvents (dh4? : Option SignalPqxdh.Bytes) : List AllocEvent :=
  stage3AfterDh4Events dh4? ++ deriveKeysAEvents

/-- Cumulative allocator events across Stage 3 (`+0x0760 → +0x10a4`) on the `Ok` path. -/
def stage3OkEvents (dh4? : Option SignalPqxdh.Bytes) : List AllocEvent :=
  stage3AfterKemBoxEvents dh4? ++ deriveKeysEvents

/-- Splits `FitsEvents` for `stage3OkEvents` into the six per-step `FitsEvents` obligations. -/
theorem fitsEvents_stage3_of_okEvents [LibsignalPlacement]
    {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {W : CliHooks} {X : UnreachedPqxdhPrimitives} {x : InitGhost}
    {be : PreKeyBundleFields} {kp : IdentityKeyPair} {ekASk ekAPk : List (BitVec 8)}
    {pqspkPtr : BitVec 64} {opkId : BitVec 32} {s0 s3 : State}
    (hs3 : AtStage3Placed W X x be kp ekASk ekAPk pqspkPtr opkId s0 s3)
    (hFit : FitsEvents M lim st (stage3OkEvents (stage3Dh4Opt X W kp be x.coins))) :
    FitsEvents M lim st (rustAllocEvents 192 1) ∧
      FitsEvents M lim (M.stepEvents (rustAllocEvents 192 1) st)
        (s3CalcAgreeEvents X W (toU8 kp.privateKey.bytes.toList)
          (toU8 x.bundle.spk.bytes.toList)) ∧
      FitsEvents M lim (M.stepEvents stage3AfterDh1Events st)
        (s3CalcAgreeEvents X W (toU8 ekASk) (toU8 x.bundle.idKey.publicKey.bytes.toList)) ∧
      FitsEvents M lim (M.stepEvents stage3AfterDh2Events st)
        (s3CalcAgreeEvents X W (toU8 ekASk) (toU8 x.bundle.spk.bytes.toList)) ∧
      FitsEvents M lim (M.stepEvents stage3AfterDh3Events st)
        (s3Dh4CalcAgreeEvents X W ekASk x.bundle.opk) ∧
      FitsEvents M lim
        (M.stepEvents (stage3AfterDh4Events (stage3Dh4Opt X W kp be x.coins)) st)
        deriveKeysAEvents := by
  set dh4Opt := stage3Dh4Opt X W kp be x.coins
  have ⟨hPreKem, _⟩ :=
    (fitsEvents_append M lim (stage3AfterKemBoxEvents dh4Opt) deriveKeysEvents st).mp hFit
  have ⟨hPre4, hFitKemBox⟩ :=
    (fitsEvents_append M lim (stage3AfterDh4Events dh4Opt) deriveKeysAEvents st).mp hPreKem
  have ⟨hPre3, hFitOpt4⟩ :=
    (fitsEvents_append M lim stage3AfterDh3Events (dh4OptEvents dh4Opt) st).mp hPre4
  have ⟨hPre2, hFitOpt3⟩ :=
    (fitsEvents_append M lim stage3AfterDh2Events dh3StepOkEvents st).mp hPre3
  have ⟨hPre1, hFitOpt2⟩ :=
    (fitsEvents_append M lim stage3AfterDh1Events dh2OkEvents st).mp hPre2
  have ⟨hFit192, hFitDh1⟩ :
      FitsEvents M lim st (rustAllocEvents 192 1) ∧
        FitsEvents M lim (M.stepEvents (rustAllocEvents 192 1) st)
          (s3CalcAgreeEvents X W (toU8 kp.privateKey.bytes.toList)
            (toU8 x.bundle.spk.bytes.toList)) :=
    fitsEvents_dh1_of_okEvents hPre1
  have hFitDh2 :
      FitsEvents M lim (M.stepEvents stage3AfterDh1Events st)
        (s3CalcAgreeEvents X W (toU8 ekASk) (toU8 x.bundle.idKey.publicKey.bytes.toList)) :=
    fitsEvents_dh2_of_okEvents hFitOpt2
  have hFitDh3 :
      FitsEvents M lim (M.stepEvents stage3AfterDh2Events st)
        (s3CalcAgreeEvents X W (toU8 ekASk) (toU8 x.bundle.spk.bytes.toList)) :=
    fitsEvents_s3CalcAgreeEvents_of_alloc32
      ((fitsEvents_append M lim (rustAllocEvents 32 1) (rustDeallocEvents 32 1)
        (M.stepEvents stage3AfterDh2Events st)).mp hFitOpt3).1
  have hFitDh4 :
      FitsEvents M lim (M.stepEvents stage3AfterDh3Events st)
        (s3Dh4CalcAgreeEvents X W ekASk x.bundle.opk) := by
    rcases hopk : x.bundle.opk with _ | ⟨oid, ok⟩
    · trivial
    · have hsome := dh4_some_eq X ⟨W.C, W.Q⟩ kp x.bundle be x.coins ekASk oid ok
        hs3.bundleEq hopk hs3.ekPairEq.1
      dsimp only [ofSignalPqxdhPrimitives] at hsome
      have hOpt4' :
          FitsEvents M lim (M.stepEvents stage3AfterDh3Events st)
            (rustAllocEvents 32 1 ++ rustDeallocEvents 32 1) := by
        simpa only [dh4Opt, stage3Dh4Opt, hsome, dh4OptEvents] using hFitOpt4
      exact fitsEvents_s3CalcAgreeEvents_of_alloc32
        ((fitsEvents_append M lim (rustAllocEvents 32 1) (rustDeallocEvents 32 1)
          (M.stepEvents stage3AfterDh3Events st)).mp hOpt4').1
  exact ⟨hFit192, hFitDh1, hFitDh2, hFitDh3, hFitDh4, hFitKemBox⟩

/-! ## `HandshakeKeys::derive` (`+0x1044 → +0x10a4`) -/

set_option maxHeartbeats 1200000 in
/-- Budget-threaded `<HandshakeKeys>::derive` (`+0x1044 → +0x10a4`, general `dh4?`),
parameterized by a Block `59` `subroutine_ok` witness. -/
theorem derive_keys_of_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {st0 st : M.σ} {be : PreKeyBundleFields} {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)} {pqspkPtr secretsPtr ssBoxPtr kemCtPtr : BitVec 64}
    {opkId : BitVec 32} {dh1 dh2 dh3 : SignalPqxdh.Bytes} {dh4? : Option SignalPqxdh.Bytes}
    {stk : Nat} {s0 s3 sg : State} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hDerive : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 59)
      (withLsCodeRoLoaded lsmpl
        (handshakeKeysDerivePlacedBaseSpec M
          (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) A lim)))
    (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hs3 : AtStage3Placed W X x be kp ekASk ekAPk pqspkPtr opkId s0 s3)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf)
    (hdh1_eq : dh1 = (modelPrims X ⟨W.C, W.Q⟩).x25519
      (initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)).ikASk
      (initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)).bundle.spkB)
    (hdh1_nz : dh1 ≠ List.replicate 32 0) (hdh1_len : dh1.length = 32)
    (hdh2_eq : dh2 = (modelPrims X ⟨W.C, W.Q⟩).x25519
      (initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)).ekASk
      (initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)).bundle.ikB)
    (hdh2_nz : dh2 ≠ List.replicate 32 0) (hdh2_len : dh2.length = 32)
    (hdh3_eq : dh3 = (modelPrims X ⟨W.C, W.Q⟩).x25519
      (initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)).ekASk
      (initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)).bundle.spkB)
    (hdh3_nz : dh3 ≠ List.replicate 32 0) (hdh3_len : dh3.length = 32)
    (hdh4_eq : dh4? = ((initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be
      (padCoins x.coins)).bundle.opkB?.map fun (_, opkPk) =>
        (modelPrims X ⟨W.C, W.Q⟩).x25519
          (initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)).ekASk
          opkPk))
    (hdh4_nz : SignalPqxdh.dhOptNonZero dh4? = true)
    (hdh4_len : ∀ d, dh4? = some d → d.length = 32)
    (hkemNonNull : kemCtPtr ≠ 0#64)
    (hctrl : InInitiatePlaced s0 sg 0x1044) (htr : sg.trace = s0.trace)
    (hx20 : sg.readReg64 (.gpr 20#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x348#64)
    (hx21 : sg.readReg64 (.gpr 21#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x388#64)
    (hx26 : sg.readReg64 (.gpr 26#5) = ssBoxPtr)
    (hnext : ∀ (s4 : State) (dk : SignalPqxdh.DRKey) (hdr : SignalPqxdh.HandshakeHdr)
        (kemCtBytes hkSlotBytes : List (BitVec 8)) (kemCtPtr : BitVec 64),
      AtStage4Placed W X x be kp ekASk ekAPk dk hdr kemCtBytes hkSlotBytes pqspkPtr kemCtPtr opkId
        s0 s4 →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s4
        (stage4MemPlaced A lim (M.stepEvents deriveKeysEvents st) x kp ekASk ekAPk kemCtBytes
          hkSlotBytes pqspkPtr kemCtPtr opkId stk s0 s4)
        Q Qp oom) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    let t := padCoins x.coins
    let ct := (W.Q.encaps be.kpkPub (initiateKemCoins t)).1
    let ss := (W.Q.encaps be.kpkPub (initiateKemCoins t)).2
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sg
      (S3InvPrefixPlaced A x s0 ∗ coinsCursorAtPlaced x.coinsP x.coins 160 ∗
        A.pool lim st sg ∗ stackAt fsp pqxdhEntryStack ∗
        memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
          (stk - cliInitiateFrame - pqxdhEntryStack) ∗
        A.live secretsPtr 192 1 ∗
        (secretsPtr ↦ₛ bytesToBv8 (dhPrefix dh1 dh2 dh3 dh4?)) ∗
        dhRemAt secretsPtr dh4? ∗
        A.live ssBoxPtr 32 1 ∗ (ssBoxPtr ↦ₛ ss.toList) ∗
        memRegion fsp 0x60 ∗
        ((fsp + 0x60#64) ↦₆₄ kemCtPtr) ∗ ((fsp + 0x68#64) ↦₆₄ 1569#64) ∗
        A.live kemCtPtr 1569 1 ∗ (kemCtPtr ↦ₛ (8#8 :: ct.toList)) ∗
        ((fsp + 0x70#64) ↦₆₄ (fsp + 0x408#64)) ∗ ((fsp + 0x78#64) ↦₆₄ (fsp + 0x3c8#64)) ∗
        stage3KeySlotsAt A.repAlloc fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
        memRegion (fsp + 0x930#64) 8 ∗ memRegion (fsp + 0x938#64) 0x20 ∗
        memRegion (fsp + 0x958#64) 0x48 ∗ ((fsp + 0x9a0#64) ↦ₛ ekASk) ∗
        ((fsp + 0x9c0#64) ↦ₛ x.bundle.kpk) ∗ memRegion (fsp + 0xfe0#64) 0xc80 ∗
        ((fsp + 0x1c60#64) ↦₆₄ 192#64) ∗ ((fsp + 0x1c68#64) ↦₆₄ secretsPtr) ∗
        ((fsp + 0x1c70#64) ↦₆₄ dhLenWord dh4?) ∗ memRegion (fsp + 0x1c78#64) 0x18)
      Q Qp oom := by
  dsimp only
  cases dh4? with
  | none =>
    exact derive_keys_none_of_ok hh hDerive hstk hstk64 hs3 hpanic
      hdh1_eq hdh1_nz hdh1_len hdh2_eq hdh2_nz hdh2_len hdh3_eq hdh3_nz hdh3_len
      hdh4_eq.symm hkemNonNull hctrl htr hx20 hx21 hx26 hnext
  | some dh4 =>
    dsimp only [dhPrefix, dhRemAt, dhLenWord]
    set fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    set t := padCoins x.coins
    set ct := (W.Q.encaps be.kpkPub (initiateKemCoins t)).1
    set ss := (W.Q.encaps be.kpkPub (initiateKemCoins t)).2
    obtain ⟨_, _, hkpkLen, _, _, _, _, _⟩ := bundleEOf_props hs3.bundleEq
    have hekASkLen : ekASk.length = 32 := by rw [hs3.ekPairEq.1]; exact List.Vector.toList_length _
    have hsub_pq : pqxdhEntryStack ≤ stk - cliInitiateFrame :=
      Nat.le_trans (by decide) (stk_sub_ge_base hstk)
    have h930_split :
        memRegion (fsp + 0x930#64) 8 ∗ memRegion (fsp + 0x938#64) 0x20 ∗
          memRegion (fsp + 0x958#64) 0x48 =
          memRegion (fsp + 0x930#64) 100 ∗ memRegion (fsp + 0x994#64) 12 := by
      rw [memRegion_merge_at (fsp + 0x938#64) 0x20 0x48 (fsp + 0x958#64) (by clear * -; bv_omega) (by decide),
          memRegion_merge_at (fsp + 0x930#64) 8 104 (fsp + 0x938#64) (by clear * -; bv_omega) (by decide),
          memRegion_merge_at (fsp + 0x930#64) 100 12 (fsp + 0x994#64) (by clear * -; bv_omega) (by decide)]
    have hss_bv : bytesToBv8 (vecU8 ss) = ss.toList := bytesToBv8_toU8_eq ss.toList
    have hss_u8_len : (vecU8 ss).length = 32 := e2e_vecU8_length ss
    obtain ⟨ss0, ss1, ss2, ss3, hss_cells⟩ := bytes32_exists_cells4 ss.toList_length
    have hstk_ext := stackAt_sub_split_init fsp (by decide : extHookStack ≤ pqxdhEntryStack) (by decide)
    obtain ⟨hkeysOk, hctEq, hhkEq, hctLen1569, hhkLen100⟩ :=
      stage4_keysOk_of_parts X ⟨W.C, W.Q⟩ kp be x.coins hs3.signaturesVerify
        (hdh1_eq ▸ hdh1_nz) (hdh2_eq ▸ hdh2_nz) (hdh3_eq ▸ hdh3_nz) (hdh4_eq ▸ hdh4_nz)
    have h4_len : dh4.length = 32 := hdh4_len dh4 rfl
    have hsec_len : (buildSecrets dh1 dh2 dh3 (some dh4) (vecU8 ss)).length = 192 := by
      simp [buildSecrets, F_X25519, hdh1_len, hdh2_len, hdh3_len, h4_len, hss_u8_len]
    have htake32 := buildSecrets_take32_eq dh1 dh2 dh3 (some dh4) (vecU8 ss)
    rw [hstk_ext, hss_cells ssBoxPtr, memRegion32_cells4 (secretsPtr + 160#64)]
    refine sepWPp_conseq_oom (by
      dsimp only [fsp] at h930_split ⊢
      exact sep_replace (Entails.of_eq h930_split) (by sep_frame) (Entails.refl _)) ?_
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepExists_sepConj_right]
    refine sepWPp_exists_elim_oom fun d0 => sepWPp_exists_elim_oom fun d1 =>
      sepWPp_exists_elim_oom fun d2 => sepWPp_exists_elim_oom fun d3 => ?_
    obtain ⟨halign0, hx29_0, hfsp0⟩ := hctrl.step_ctx fsp
    refine' s3_block_to_call_vm_placed hh
      (lsρ lsRustDeallocSymCli)
      0x107c (Φ := fun sm =>
        sm.readReg64 .x0 = ssBoxPtr ∧ sm.readReg64 .x1 = 32#64 ∧ sm.readReg64 .x2 = 1#64 ∧
        sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧ sm.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
        sm.readReg64 (.gpr 22#5) = fsp + 0x900#64 ∧ sm.readReg64 (.gpr 25#5) = secretsPtr ∧
        sm.readReg64 (.gpr 27#5) = 192#64 ∧ sm.readReg64 (.gpr 28#5) = 160#64)
      hctrl ?_ ?_; rotate_left 1
    · have hpc : sg.pc = (blkPl_521).base + 0x1044#64 := hctrl.pc; have hrun := hctrl.run
      dsimp only [initPcPlaced, initEntryPlaced, initProgPlaced, initProgExtPlaced, lsProg_521, BitVec.ofNat_eq_ofNat] at ⊢
      (try dsimp only [fsp] at *); rw [← hctrl.sp] at *
      try simp only [arm64_norm, wp_norm] at hx20 hx21 hx26
      by_vm_steps (
        wp_steps
        refine s3_done_call_vm (by wp_norm_lhs) (Entails.refl _)
          ⟨by simp only [hx26, arm64_norm, wp_norm], by wp_norm_goal, by wp_norm_goal,
           by simp only [hx20, arm64_norm, wp_norm], by simp only [hx21, arm64_norm, wp_norm],
           by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩
          (hpc := by (try wp_norm_goal); try (clear * -; bv_omega))
          (hlr := by (try wp_norm_goal); try (clear * -; bv_omega)))
    · intro sm1 hvm1 hc1 hp1 hl1 ht1 ⟨hx0_1, hx1_1, hx2_1, hx20_1, hx21_1, hx22_1, hx25_1, hx27_1, hx28_1⟩
      have hpool1 : A.pool lim st sg = A.pool lim st sm1 :=
        (A.pool_transport lim st sg sm1 hvm1).symm
      rw [hctrl.sp] at *; try iterate 6 rw [BitVec.add_comm _ fsp]; try iterate 6 rw [BitVec.add_comm _ (s0.sp - BitVec.ofNat 64 cliInitiateFrame)]
      have htr1 := ht1.trans htr
      have hbox32 := cells4_to_memRegion32 ssBoxPtr ss0 ss1 ss2 ss3
      have hss_fold160 :
          ((secretsPtr + 160#64) ↦₆₄ ss0) ∗ ((secretsPtr + 168#64) ↦₆₄ ss1) ∗
            ((secretsPtr + 176#64) ↦₆₄ ss2) ∗ ((secretsPtr + 184#64) ↦₆₄ ss3) =
            ((secretsPtr + 160#64) ↦ₛ bytesToBv8 (vecU8 ss)) := by
        simpa only [BitVec.add_assoc, BitVec.reduceAdd, hss_bv] using
          (hss_cells (secretsPtr + 160#64)).symm
      have happ160 :
          (secretsPtr ↦ₛ bytesToBv8 (F_X25519 ++ dh1 ++ dh2 ++ dh3 ++ dh4)) ∗
            ((secretsPtr + 160#64) ↦ₛ bytesToBv8 (vecU8 ss)) =
            (secretsPtr ↦ₛ bytesToBv8 (buildSecrets dh1 dh2 dh3 (some dh4) (vecU8 ss))) :=
        append_bv8_at secretsPtr (F_X25519 ++ dh1 ++ dh2 ++ dh3 ++ dh4) (vecU8 ss) 160#64
          (by simp [F_X25519, hdh1_len, hdh2_len, hdh3_len, h4_len])
      refine s3_dealloc_stack_placed hh ssBoxPtr 32 st _
        hc1 hp1 hl1 hx0_1 (by rw [hx1_1]; decide) (by rw [hx2_1]; decide) lay32
        (by rw [hpool1, hc1.sp]; (try dsimp only [fsp]); exact sep_replace hbox32 (by sep_frame) (by sep_frame)) ?_
      intro s2 hc2 hcs2 htr_2
      rw [hc1.sp]
      let st1 := M.stepEvents (rustDeallocEvents 32 1) st
      have htr2 := htr_2.trans htr1
      have hx20_2 := hcs2.2.1.trans hx20_1; have hx21_2 := hcs2.2.2.1.trans hx21_1
      have hx22_2 := hcs2.2.2.2.1.trans hx22_1
      have hx25_2 := hcs2.2.2.2.2.2.2.1.trans hx25_1
      have hx27_2 := hcs2.2.2.2.2.2.2.2.2.1.trans hx27_1
      have hx28_2 := hcs2.2.2.2.2.2.2.2.2.2.1.trans hx28_1
      have hpack_sec : ∀ R : SepProp,
          (secretsPtr ↦ₛ bytesToBv8 (F_X25519 ++ dh1 ++ dh2 ++ dh3 ++ dh4)) ∗
            ((secretsPtr + 160#64) ↦₆₄ ss0) ∗ ((secretsPtr + 168#64) ↦₆₄ ss1) ∗
            ((secretsPtr + 176#64) ↦₆₄ ss2) ∗ ((secretsPtr + 184#64) ↦₆₄ ss3) ∗ R =
            (secretsPtr ↦ₛ bytesToBv8 (buildSecrets dh1 dh2 dh3 (some dh4) (vecU8 ss))) ∗ R := fun R => by
        have h1 :
            ((secretsPtr + 160#64) ↦₆₄ ss0) ∗ ((secretsPtr + 168#64) ↦₆₄ ss1) ∗
              ((secretsPtr + 176#64) ↦₆₄ ss2) ∗ ((secretsPtr + 184#64) ↦₆₄ ss3) ∗ R =
              ((secretsPtr + 160#64) ↦ₛ bytesToBv8 (vecU8 ss)) ∗ R := by
          rw [← hss_fold160]; simp only [sepConj_assoc]
        rw [h1, ← sepConj_assoc, happ160]
      have hrepack_stk : ∀ (a1 a2 a3 a4 R : SepProp),
          stackAt fsp extHookStack ∗ a1 ∗ a2 ∗ a3 ∗ a4 ∗
            memRegion (fsp - BitVec.ofNat 64 pqxdhEntryStack) (pqxdhEntryStack - extHookStack) ∗ R =
            stackAt fsp pqxdhEntryStack ∗ a1 ∗ a2 ∗ a3 ∗ a4 ∗ R := fun a1 a2 a3 a4 R => by
        rw [hstk_ext]; sep_ac_rfl
      dsimp only [fsp, ss] at hpack_sec hrepack_stk ⊢
      rw [hpack_sec, hrepack_stk]
      obtain ⟨halign2, hx29_2, hfsp2⟩ := hc2.step_ctx fsp
      refine' s3_block_to_call_vm_placed hh
        (lsmpl.base 59)
        0x1090 (Φ := fun sm =>
          sm.readReg64 .x8 = fsp + 0x930#64 ∧ sm.readReg64 .x0 = secretsPtr ∧
          sm.readReg64 .x1 = 192#64 ∧
          sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧ sm.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
          sm.readReg64 (.gpr 22#5) = fsp + 0x900#64 ∧ sm.readReg64 (.gpr 25#5) = secretsPtr ∧
          sm.readReg64 (.gpr 27#5) = 192#64)
        hc2 ?_ ?_; rotate_left 1
      · have hpc : s2.pc = (blkPl_521).base + 0x107c#64 := hc2.pc; have hrun := hc2.run
        dsimp only [initPcPlaced, initEntryPlaced, initProgPlaced, initProgExtPlaced, lsProg_521, BitVec.ofNat_eq_ofNat] at ⊢
        (try dsimp only [fsp] at *); rw [← hc2.sp] at *
        try simp only [arm64_norm, wp_norm] at hx20_2 hx21_2 hx22_2 hx25_2 hx27_2 hx28_2
        by_vm_steps (
          wp_steps
          refine s3_done_call_vm (by wp_norm_lhs) (Entails.refl _)
            ⟨by wp_norm_goal, by simp only [hx25_2, arm64_norm, wp_norm],
             by simp only [hx28_2, arm64_norm, wp_norm],
             by simp only [hx20_2, arm64_norm, wp_norm], by simp only [hx21_2, arm64_norm, wp_norm],
             by simp only [hx22_2, arm64_norm, wp_norm], by simp only [hx25_2, arm64_norm, wp_norm],
             by simp only [hx27_2, arm64_norm, wp_norm]⟩
            (hpc := by (try wp_norm_goal); try (clear * -; bv_omega))
            (hlr := by (try wp_norm_goal); try (clear * -; bv_omega)))
      · intro sm3 hvm3 hc3 hp3 hl3 ht3 ⟨hx8_3, hx0_3, hx1_3, hx20_3, hx21_3, hx22_3, hx25_3, hx27_3⟩
        have hpool3 : A.pool lim st1 s2 = A.pool lim st1 sm3 :=
          (A.pool_transport lim st1 s2 sm3 hvm3).symm
        rw [hc2.sp] at *; try iterate 6 rw [BitVec.add_comm _ fsp]; try iterate 6 rw [BitVec.add_comm _ (s0.sp - BitVec.ofNat 64 cliInitiateFrame)]
        have htr3 := ht3.trans htr2
        refine s3_call_placed hh hDerive
          (⟨secretsPtr, buildSecrets dh1 dh2 dh3 (some dh4) (vecU8 ss), fsp + 0x930#64⟩, st1) _
          hc3 htr3 hp3 hl3 hpanic
          (by
            dsimp only [handshakeKeysDerivePlacedBaseSpec, st1] at hpool3 ⊢
            simp only [hc3.sp, sepConj_assoc]
            rw [hpool3]
            refine Entails.pure_right ⟨hx8_3, hx0_3, by rw [hx1_3, hsec_len]; decide,
              Or.inr hsec_len, htake32⟩ ?_
            dsimp only [fsp, ss, t] at *
            sep_frame) ?_ ?_ ?_ ?_
        · intro _ _ h; simp [handshakeKeysDerivePlacedBaseSpec, Spec.onPanic] at h
        · intro _ _ _ h; simp [handshakeKeysDerivePlacedBaseSpec, Spec.onExit] at h
        · intro _ _ h; simp [handshakeKeysDerivePlacedBaseSpec, Spec.onOom] at h
        · intro s4a _ _ _ hcs4 _ hof4
          dsimp only [handshakeKeysDerivePlacedBaseSpec]
          simp only [hc3.sp, sepConj_assoc]
          refine sepWPp_pure_elim_oom fun ⟨_, htr_4⟩ => ?_
          have hc4 := hof4 htr_4
          have htr4 := htr_4.trans htr3
          have hx20_4 := hcs4.2.1.trans hx20_3; have hx21_4 := hcs4.2.2.1.trans hx21_3
          have hx22_4 := hcs4.2.2.2.1.trans hx22_3
          have hx25_4 := hcs4.2.2.2.2.2.2.1.trans hx25_3
          have hx27_4 := hcs4.2.2.2.2.2.2.2.2.1.trans hx27_3
          obtain ⟨halign4, hx29_4, hfsp4⟩ := hc4.step_ctx fsp
          refine' s3_block_to_call_vm_placed hh
            (lsρ lsRustDeallocSymCli)
            0x10a4 (Φ := fun sm =>
              sm.readReg64 .x0 = secretsPtr ∧ sm.readReg64 .x1 = 192#64 ∧ sm.readReg64 .x2 = 1#64 ∧
              sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧
              sm.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
              sm.readReg64 (.gpr 22#5) = fsp + 0x900#64)
            hc4 ?_ ?_; rotate_left 1
          · have hpc : s4a.pc = (blkPl_521).base + 0x1090#64 := hc4.pc; have hrun := hc4.run
            dsimp only [initPcPlaced, initEntryPlaced, initProgPlaced, initProgExtPlaced, lsProg_521, BitVec.ofNat_eq_ofNat] at ⊢
            (try dsimp only [fsp] at *); rw [← hc4.sp] at *
            try simp only [arm64_norm, wp_norm] at hx20_4 hx21_4 hx22_4 hx25_4 hx27_4
            by_vm_steps (
              wp_steps
              refine s3_done_call_vm (by wp_norm_lhs) (Entails.refl _)
                ⟨by simp only [hx25_4, arm64_norm, wp_norm], by simp only [hx27_4, arm64_norm, wp_norm],
                 by wp_norm_goal,
                 by simp only [hx20_4, arm64_norm, wp_norm], by simp only [hx21_4, arm64_norm, wp_norm],
                 by simp only [hx22_4, arm64_norm, wp_norm]⟩
                (hpc := by (try wp_norm_goal); try (clear * -; bv_omega))
                (hlr := by (try wp_norm_goal); try (clear * -; bv_omega)))
          · intro sm5 hvm5 hc5 hp5 hl5 ht5 ⟨hx0_5, hx1_5, hx2_5, hx20_5, hx21_5, hx22_5⟩
            have hpool5 : A.pool lim st1 s4a = A.pool lim st1 sm5 :=
              (A.pool_transport lim st1 s4a sm5 hvm5).symm
            rw [hc4.sp] at *; try iterate 6 rw [BitVec.add_comm _ fsp]; try iterate 6 rw [BitVec.add_comm _ (s0.sp - BitVec.ofNat 64 cliInitiateFrame)]
            have htr5 := ht5.trans htr4
            have hsec192 :
                (secretsPtr ↦ₛ bytesToBv8 (buildSecrets dh1 dh2 dh3 (some dh4) (vecU8 ss))) ⊢
                  memRegion secretsPtr 192 :=
              pointsToBytes_entails_memRegion_len ((bytesToBv8_length _).trans hsec_len)
            refine s3_dealloc_stack_placed hh secretsPtr 192 st1 _
              hc5 hp5 hl5 hx0_5 (by rw [hx1_5]; decide) (by rw [hx2_5]; decide) lay192
              (by dsimp only [st1] at hpool5 ⊢
                  dsimp only [fsp, ss, t] at *
                  rw [hpool5, hc5.sp, hstk_ext]
                  exact sep_replace hsec192 (by sep_frame) (by sep_frame)) ?_
            intro s_end hc_end hcs_end htr_end
            rw [hc5.sp]
            have htr_final := htr_end.trans htr5
            have hfs_final : s_end.fs.files = x.F :=
              hc_end.files0.trans hs3.ctrl.files0.symm |>.trans hs3.files
            have hstk_full :
                memRegion (fsp - BitVec.ofNat 64 pqxdhEntryStack) (pqxdhEntryStack - extHookStack) ∗
                  stackAt fsp extHookStack ∗
                  memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
                    (stk - cliInitiateFrame - pqxdhEntryStack) =
                  stackAt fsp (stk - cliInitiateFrame) := by
              rw [← sepConj_assoc, ← hstk_ext, sepConj_comm,
                  ← stackAt_sub_split_init fsp hsub_pq (by omega)]
            have htail := tail_locals_collapse fsp hekASkLen hkpkLen secretsPtr 160#64
            subst hdh1_eq hdh2_eq hdh3_eq
            dsimp only [t] at hdh4_eq
            conv at hhkEq => lhs; rw [← hdh4_eq]
            refine sepWPp_conseq_oom ?_
              (hnext s_end _ _ (8#8 :: ct.toList) _ kemCtPtr
                { ctrl := hc_end, trace := htr_final, files := hfs_final, x8 := hs3.x8,
                  bundleEq := hs3.bundleEq, trustedOk := hs3.trustedOk, kpOk := hs3.kpOk,
                  ekPairEq := hs3.ekPairEq, opkIdEq := hs3.opkIdEq,
                  keysOk := hkeysOk, kemCtEq := hctEq, hkSlotEq := rfl,
                  pqspkNonNull := hs3.pqspkNonNull, kemCtNonNull := hkemNonNull,
                  x20 := hcs_end.2.1.trans hx20_5, x21 := hcs_end.2.2.1.trans hx21_5,
                  x22 := hcs_end.2.2.2.1.trans hx22_5 })
            unfold S3InvPrefixPlaced; dsimp only [stage4MemPlaced, st1]
            rw [stepEvents_deriveKeysEvents M st]
            refine Entails.pure_right ⟨hctLen1569, hhkLen100⟩ ?_
            dsimp only [fsp, ct, ss, t] at hhkEq hstk_full htail ⊢
            rw [hhkEq]
            refine sep_replace htail (by sep_frame) ?_
            exact sep_replace (Entails.of_eq hstk_full) (by sep_frame) (by sep_frame)

theorem derive_keys_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {InitStateEnv : Params → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {st0 st : M.σ} {be : PreKeyBundleFields} {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)} {pqspkPtr secretsPtr ssBoxPtr kemCtPtr : BitVec 64}
    {opkId : BitVec 32} {dh1 dh2 dh3 : SignalPqxdh.Bytes} {dh4? : Option SignalPqxdh.Bytes}
    {stk : Nat} {s0 s3 sg : State} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hLocal : InitLocalCalleesPlaced A lim InitStateEnv mmpl gh W stk)
    (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hs3 : AtStage3Placed W X x be kp ekASk ekAPk pqspkPtr opkId s0 s3)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf)
    (hdh1_eq : dh1 = (modelPrims X ⟨W.C, W.Q⟩).x25519
      (initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)).ikASk
      (initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)).bundle.spkB)
    (hdh1_nz : dh1 ≠ List.replicate 32 0) (hdh1_len : dh1.length = 32)
    (hdh2_eq : dh2 = (modelPrims X ⟨W.C, W.Q⟩).x25519
      (initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)).ekASk
      (initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)).bundle.ikB)
    (hdh2_nz : dh2 ≠ List.replicate 32 0) (hdh2_len : dh2.length = 32)
    (hdh3_eq : dh3 = (modelPrims X ⟨W.C, W.Q⟩).x25519
      (initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)).ekASk
      (initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)).bundle.spkB)
    (hdh3_nz : dh3 ≠ List.replicate 32 0) (hdh3_len : dh3.length = 32)
    (hdh4_eq : dh4? = ((initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be
      (padCoins x.coins)).bundle.opkB?.map fun (_, opkPk) =>
        (modelPrims X ⟨W.C, W.Q⟩).x25519
          (initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)).ekASk
          opkPk))
    (hdh4_nz : SignalPqxdh.dhOptNonZero dh4? = true)
    (hdh4_len : ∀ d, dh4? = some d → d.length = 32)
    (hkemNonNull : kemCtPtr ≠ 0#64)
    (hctrl : InInitiatePlaced s0 sg 0x1044) (htr : sg.trace = s0.trace)
    (hx20 : sg.readReg64 (.gpr 20#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x348#64)
    (hx21 : sg.readReg64 (.gpr 21#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x388#64)
    (hx26 : sg.readReg64 (.gpr 26#5) = ssBoxPtr)
    (hnext : ∀ (s4 : State) (dk : SignalPqxdh.DRKey) (hdr : SignalPqxdh.HandshakeHdr)
        (kemCtBytes hkSlotBytes : List (BitVec 8)) (kemCtPtr : BitVec 64),
      AtStage4Placed W X x be kp ekASk ekAPk dk hdr kemCtBytes hkSlotBytes pqspkPtr kemCtPtr opkId
        s0 s4 →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s4
        (stage4MemPlaced A lim (M.stepEvents deriveKeysEvents st) x kp ekASk ekAPk kemCtBytes
          hkSlotBytes pqspkPtr kemCtPtr opkId stk s0 s4)
        Q Qp oom) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    let t := padCoins x.coins
    let ct := (W.Q.encaps be.kpkPub (initiateKemCoins t)).1
    let ss := (W.Q.encaps be.kpkPub (initiateKemCoins t)).2
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sg
      (S3InvPrefixPlaced A x s0 ∗ coinsCursorAtPlaced x.coinsP x.coins 160 ∗
        A.pool lim st sg ∗ stackAt fsp pqxdhEntryStack ∗
        memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
          (stk - cliInitiateFrame - pqxdhEntryStack) ∗
        A.live secretsPtr 192 1 ∗
        (secretsPtr ↦ₛ bytesToBv8 (dhPrefix dh1 dh2 dh3 dh4?)) ∗
        dhRemAt secretsPtr dh4? ∗
        A.live ssBoxPtr 32 1 ∗ (ssBoxPtr ↦ₛ ss.toList) ∗
        memRegion fsp 0x60 ∗
        ((fsp + 0x60#64) ↦₆₄ kemCtPtr) ∗ ((fsp + 0x68#64) ↦₆₄ 1569#64) ∗
        A.live kemCtPtr 1569 1 ∗ (kemCtPtr ↦ₛ (8#8 :: ct.toList)) ∗
        ((fsp + 0x70#64) ↦₆₄ (fsp + 0x408#64)) ∗ ((fsp + 0x78#64) ↦₆₄ (fsp + 0x3c8#64)) ∗
        stage3KeySlotsAt A.repAlloc fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
        memRegion (fsp + 0x930#64) 8 ∗ memRegion (fsp + 0x938#64) 0x20 ∗
        memRegion (fsp + 0x958#64) 0x48 ∗ ((fsp + 0x9a0#64) ↦ₛ ekASk) ∗
        ((fsp + 0x9c0#64) ↦ₛ x.bundle.kpk) ∗ memRegion (fsp + 0xfe0#64) 0xc80 ∗
        ((fsp + 0x1c60#64) ↦₆₄ 192#64) ∗ ((fsp + 0x1c68#64) ↦₆₄ secretsPtr) ∗
        ((fsp + 0x1c70#64) ↦₆₄ dhLenWord dh4?) ∗ memRegion (fsp + 0x1c78#64) 0x18)
      Q Qp oom :=
  derive_keys_of_ok hh (hLocal.handshakeDerive X) hstk hstk64 hs3 hpanic
    hdh1_eq hdh1_nz hdh1_len hdh2_eq hdh2_nz hdh2_len hdh3_eq hdh3_nz hdh3_len
    hdh4_eq hdh4_nz hdh4_len hkemNonNull hctrl htr hx20 hx21 hx26 hnext

theorem derive_keys_a4_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {InitStateEnv : Params → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {st0 st : M.σ} {be : PreKeyBundleFields} {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)} {pqspkPtr secretsPtr ssBoxPtr kemCtPtr : BitVec 64}
    {opkId : BitVec 32} {dh1 dh2 dh3 : SignalPqxdh.Bytes} {dh4? : Option SignalPqxdh.Bytes}
    {stk : Nat} {s0 s3 sg : State} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (ha4 : SubsetA4InitCalleesPlaced A lim InitStateEnv mmpl gh W)
    (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hs3 : AtStage3Placed W X x be kp ekASk ekAPk pqspkPtr opkId s0 s3)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf)
    (hdh1_eq : dh1 = (modelPrims X ⟨W.C, W.Q⟩).x25519
      (initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)).ikASk
      (initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)).bundle.spkB)
    (hdh1_nz : dh1 ≠ List.replicate 32 0) (hdh1_len : dh1.length = 32)
    (hdh2_eq : dh2 = (modelPrims X ⟨W.C, W.Q⟩).x25519
      (initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)).ekASk
      (initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)).bundle.ikB)
    (hdh2_nz : dh2 ≠ List.replicate 32 0) (hdh2_len : dh2.length = 32)
    (hdh3_eq : dh3 = (modelPrims X ⟨W.C, W.Q⟩).x25519
      (initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)).ekASk
      (initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)).bundle.spkB)
    (hdh3_nz : dh3 ≠ List.replicate 32 0) (hdh3_len : dh3.length = 32)
    (hdh4_eq : dh4? = ((initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be
      (padCoins x.coins)).bundle.opkB?.map fun (_, opkPk) =>
        (modelPrims X ⟨W.C, W.Q⟩).x25519
          (initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)).ekASk
          opkPk))
    (hdh4_nz : SignalPqxdh.dhOptNonZero dh4? = true)
    (hdh4_len : ∀ d, dh4? = some d → d.length = 32)
    (hkemNonNull : kemCtPtr ≠ 0#64)
    (hctrl : InInitiatePlaced s0 sg 0x1044) (htr : sg.trace = s0.trace)
    (hx20 : sg.readReg64 (.gpr 20#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x348#64)
    (hx21 : sg.readReg64 (.gpr 21#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x388#64)
    (hx26 : sg.readReg64 (.gpr 26#5) = ssBoxPtr)
    (hnext : ∀ (s4 : State) (dk : SignalPqxdh.DRKey) (hdr : SignalPqxdh.HandshakeHdr)
        (kemCtBytes hkSlotBytes : List (BitVec 8)) (kemCtPtr : BitVec 64),
      AtStage4Placed W X x be kp ekASk ekAPk dk hdr kemCtBytes hkSlotBytes pqspkPtr kemCtPtr opkId
        s0 s4 →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s4
        (stage4MemPlaced A lim (M.stepEvents deriveKeysEvents st) x kp ekASk ekAPk kemCtBytes
          hkSlotBytes pqspkPtr kemCtPtr opkId stk s0 s4)
        Q Qp oom) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    let t := padCoins x.coins
    let ct := (W.Q.encaps be.kpkPub (initiateKemCoins t)).1
    let ss := (W.Q.encaps be.kpkPub (initiateKemCoins t)).2
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sg
      (S3InvPrefixPlaced A x s0 ∗ coinsCursorAtPlaced x.coinsP x.coins 160 ∗
        A.pool lim st sg ∗ stackAt fsp pqxdhEntryStack ∗
        memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
          (stk - cliInitiateFrame - pqxdhEntryStack) ∗
        A.live secretsPtr 192 1 ∗
        (secretsPtr ↦ₛ bytesToBv8 (dhPrefix dh1 dh2 dh3 dh4?)) ∗
        dhRemAt secretsPtr dh4? ∗
        A.live ssBoxPtr 32 1 ∗ (ssBoxPtr ↦ₛ ss.toList) ∗
        memRegion fsp 0x60 ∗
        ((fsp + 0x60#64) ↦₆₄ kemCtPtr) ∗ ((fsp + 0x68#64) ↦₆₄ 1569#64) ∗
        A.live kemCtPtr 1569 1 ∗ (kemCtPtr ↦ₛ (8#8 :: ct.toList)) ∗
        ((fsp + 0x70#64) ↦₆₄ (fsp + 0x408#64)) ∗ ((fsp + 0x78#64) ↦₆₄ (fsp + 0x3c8#64)) ∗
        stage3KeySlotsAt A.repAlloc fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
        memRegion (fsp + 0x930#64) 8 ∗ memRegion (fsp + 0x938#64) 0x20 ∗
        memRegion (fsp + 0x958#64) 0x48 ∗ ((fsp + 0x9a0#64) ↦ₛ ekASk) ∗
        ((fsp + 0x9c0#64) ↦ₛ x.bundle.kpk) ∗ memRegion (fsp + 0xfe0#64) 0xc80 ∗
        ((fsp + 0x1c60#64) ↦₆₄ 192#64) ∗ ((fsp + 0x1c68#64) ↦₆₄ secretsPtr) ∗
        ((fsp + 0x1c70#64) ↦₆₄ dhLenWord dh4?) ∗ memRegion (fsp + 0x1c78#64) 0x18)
      Q Qp oom :=
  derive_keys_of_ok hh (handshakeDerive_cli_placed_ok mmpl gh W X ha4) hstk hstk64 hs3 hpanic
    hdh1_eq hdh1_nz hdh1_len hdh2_eq hdh2_nz hdh2_len hdh3_eq hdh3_nz hdh3_len
    hdh4_eq hdh4_nz hdh4_len hkemNonNull hctrl htr hx20 hx21 hx26 hnext

/-! ## Full Stage 3 Composition (`+0x0760 → +0x10a4`) -/

/-- Full budget-threaded Stage 3 composition (`+0x0760 → +0x10a4` and zero-DH unwind exits). -/
theorem stage3_all_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {InitStateEnv : Params → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {st0 st : M.σ} {be : PreKeyBundleFields} {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)} {pqspkPtr : BitVec 64} {opkId : BitVec 32}
    {stk : Nat} {s0 s3 : State}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hCoins : ∀ {cStk : Nat}, cliCoinsFillStack ≤ cStk → cStk ≤ 2 ^ 63 →
      subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 618)
        (withLsCodeRoLoaded lsmpl (coinsFillSpecPlacedW3 cStk)))
    (hLocal : InitLocalCalleesPlaced A lim InitStateEnv mmpl gh W stk)
    (hFit192 : FitsEvents M lim st (rustAllocEvents 192 1))
    (hFitDh1 : FitsEvents M lim (M.stepEvents (rustAllocEvents 192 1) st)
      (s3CalcAgreeEvents X W (toU8 kp.privateKey.bytes.toList)
        (toU8 x.bundle.spk.bytes.toList)))
    (hFitDh2 : FitsEvents M lim (M.stepEvents stage3AfterDh1Events st)
      (s3CalcAgreeEvents X W (toU8 ekASk) (toU8 x.bundle.idKey.publicKey.bytes.toList)))
    (hFitDh3 : FitsEvents M lim (M.stepEvents stage3AfterDh2Events st)
      (s3CalcAgreeEvents X W (toU8 ekASk) (toU8 x.bundle.spk.bytes.toList)))
    (hFitDh4 : FitsEvents M lim (M.stepEvents stage3AfterDh3Events st)
      (s3Dh4CalcAgreeEvents X W ekASk x.bundle.opk))
    (hFitKemBox : FitsEvents M lim
      (M.stepEvents (stage3AfterDh4Events (stage3Dh4Opt X W kp be x.coins)) st)
      deriveKeysAEvents)
    (hEnv_dh1 :
      (let P := modelPrims X ⟨W.C, W.Q⟩
       let inp := initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)
       P.x25519 inp.ikASk inp.bundle.spkB = List.replicate 32 0) →
      ∃ evs, InitEnv x evs ∧ M.stepEvents stage3Dh1UnwindEvents st = M.stepEvents evs st0)
    (hEnv_dh2 :
      (let P := modelPrims X ⟨W.C, W.Q⟩
       let inp := initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)
       P.x25519 inp.ekASk inp.bundle.ikB = List.replicate 32 0) →
      ∃ evs, InitEnv x evs ∧ M.stepEvents stage3Dh2UnwindEvents st = M.stepEvents evs st0)
    (hEnv_dh3 :
      (let P := modelPrims X ⟨W.C, W.Q⟩
       let inp := initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)
       P.x25519 inp.ekASk inp.bundle.spkB = List.replicate 32 0) →
      ∃ evs, InitEnv x evs ∧ M.stepEvents stage3Dh3UnwindEvents st = M.stepEvents evs st0)
    (hEnv_dh4 :
      (let P := modelPrims X ⟨W.C, W.Q⟩
       let inp := initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)
       SignalPqxdh.dhOptNonZero (inp.bundle.opkB?.map fun (_, opkPk) => P.x25519 inp.ekASk opkPk) =
         false) →
      ∃ evs, InitEnv x evs ∧ M.stepEvents stage3Dh4UnwindEvents st = M.stepEvents evs st0)
    (hS : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (hcoinsLt : x.coins.length < 2 ^ 63)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hs3 : AtStage3Placed W X x be kp ekASk ekAPk pqspkPtr opkId s0 s3)
    (hpost : ∀ sf Pf, InitExitPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Q sf Pf)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf)
    (hnext : ∀ (s4 : State) (dk : SignalPqxdh.DRKey) (hdr : SignalPqxdh.HandshakeHdr)
        (kemCtBytes hkSlotBytes : List (BitVec 8)) (kemCtPtr : BitVec 64),
      AtStage4Placed W X x be kp ekASk ekAPk dk hdr kemCtBytes hkSlotBytes pqspkPtr kemCtPtr opkId
        s0 s4 →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s4
        (stage4MemPlaced A lim
          (M.stepEvents (stage3OkEvents (stage3Dh4Opt X W kp be x.coins)) st)
          x kp ekASk ekAPk kemCtBytes hkSlotBytes pqspkPtr kemCtPtr opkId stk s0 s4)
        Q Qp oom) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s3
      (stage3MemPlaced A lim st x kp ekASk ekAPk pqspkPtr opkId stk s0 s3) Q Qp oom := by
  refine dh1_step_placed_ok hh hLocal hS hstk hstk64 hs3 hFit192 hFitDh1 hEnv_dh1 hpost hpanic
    fun s_a secretsPtr dh1 hdh1_eq hdh1_nz hsecNonNull hc_a htr_a
      hx20_a hx21_a hx22_a hx24_a hx25_a hx26_a => ?_
  have hdh1_len : dh1.length = 32 := hdh1_eq ▸ modelPrims_x25519_len X ⟨W.C, W.Q⟩ _ _
  refine dh2_step_placed_ok hh hLocal hS hstk hstk64 hs3 hFitDh2
    (fun h0 =>
      let ⟨evs, hev, hst⟩ := hEnv_dh2 h0
      ⟨evs, hev, (M.stepEvents_append stage3AfterDh1Events unwind1548Events st).symm.trans hst⟩)
    hpost hpanic hdh1_len hsecNonNull hc_a htr_a hx20_a hx21_a hx22_a hx24_a hx25_a hx26_a
    fun s_b dh2 hdh2_eq hdh2_nz hc_b htr_b hx20_b hx21_b hx22_b hx24_b hx26_b => ?_
  rw [show dh1OkEvents = stage3AfterDh1Events from rfl,
    ← M.stepEvents_append stage3AfterDh1Events dh2OkEvents st,
    show stage3AfterDh1Events ++ dh2OkEvents = stage3AfterDh2Events from rfl]
  have hdh2_len : dh2.length = 32 := hdh2_eq ▸ modelPrims_x25519_len X ⟨W.C, W.Q⟩ _ _
  refine dh3_step_placed_ok hh hLocal hFitDh3
    (fun h0 =>
      let ⟨evs, hev, hst⟩ := hEnv_dh3 h0
      ⟨evs, hev,
        (stepEvents_unwind1548Events M (M.stepEvents stage3AfterDh2Events st)).trans
          ((M.stepEvents_append stage3AfterDh2Events unwind1548Events st).symm.trans hst)⟩)
    hS hstk hstk64 hs3 hpost hpanic hdh1_len hdh2_len hsecNonNull hc_b htr_b
    hx20_b hx21_b hx22_b hx24_b hx26_b
    fun s_c dh3 hdh3_eq hdh3_nz hc_c htr_c hx20_c hx21_c hx22_c hx26_c => ?_
  rw [← M.stepEvents_append stage3AfterDh2Events dh3StepOkEvents st,
    show stage3AfterDh2Events ++ dh3StepOkEvents = stage3AfterDh3Events from rfl]
  have hdh3_len : dh3.length = 32 := hdh3_eq ▸ modelPrims_x25519_len X ⟨W.C, W.Q⟩ _ _
  refine dh4_step_placed_ok hh hLocal hFitDh4
    (fun h0 =>
      let ⟨evs, hev, hst⟩ := hEnv_dh4 h0
      ⟨evs, hev,
        (stepEvents_unwind1548Events M (M.stepEvents stage3AfterDh3Events st)).trans
          ((M.stepEvents_append stage3AfterDh3Events unwind1548Events st).symm.trans hst)⟩)
    hS hstk hstk64 hs3 hpost hpanic hdh1_len hdh2_len hdh3_len hsecNonNull hc_c htr_c
    hx20_c hx21_c hx22_c hx26_c
    fun s_d dh4? hdh4_eq hdh4_nz hdh4_len hc_d htr_d hx20_d hx21_d hx22_d => ?_
  rw [← M.stepEvents_append stage3AfterDh3Events (dh4OptEvents dh4?) st,
    show stage3AfterDh3Events ++ dh4OptEvents dh4? = stage3AfterDh4Events dh4? from rfl]
  refine kem_coins_a_placed_ok hh @hCoins hcoinsLt hstk hstk64 hs3
    hc_d htr_d hx20_d hx21_d hx22_d hpanic
    fun s_e z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23
      hc_e htr_e hx20_e hx21_e => ?_
  refine kem_coins_b_placed_ok hh @hCoins hcoinsLt hpanic hc_e htr_e hx20_e hx21_e
    fun s_f hc_f htr_f hx20_f hx21_f => ?_
  refine kem_coins_c_placed_ok hh @hCoins hcoinsLt hpanic hc_f htr_f hx20_f hx21_f
    fun s_g hc_g htr_g hx20_g hx21_g hx25_g hx22_g hx26_g hx23_g hx27_g hx28_g hx24_g => ?_
  refine kem_encaps_placed_ok hh hstk hstk64 hs3 hpanic hc_g htr_g
    hx20_g hx21_g hx25_g hx22_g hx26_g hx23_g hx27_g hx28_g hx24_g
    fun s_h hc_h htr_h hx20_h hx21_h => ?_
  have hFitKemBox' :
      FitsEvents M lim (M.stepEvents (stage3AfterDh4Events dh4?) st) deriveKeysAEvents := by
    simpa only [stage3Dh4Opt, ← hdh4_eq] using hFitKemBox
  refine derive_keys_a_placed_ok hh hLocal hFitKemBox' hpanic hc_h htr_h hx20_h hx21_h
    fun s_i ssBoxPtr kemCtPtr hkemNonNull hc_i htr_i hx20_i hx21_i hx26_i => ?_
  rw [← M.stepEvents_append (stage3AfterDh4Events dh4?) deriveKeysAEvents st,
    show stage3AfterDh4Events dh4? ++ deriveKeysAEvents = stage3AfterKemBoxEvents dh4? from rfl]
  refine derive_keys_placed_ok hh hLocal hstk hstk64 hs3 hpanic
    hdh1_eq hdh1_nz hdh1_len hdh2_eq hdh2_nz hdh2_len hdh3_eq hdh3_nz hdh3_len
    hdh4_eq hdh4_nz hdh4_len hkemNonNull hc_i htr_i hx20_i hx21_i hx26_i
    fun s4 dk hdr kemCtBytes hkSlotBytes kemCtPtr' hs4 => ?_
  rw [← M.stepEvents_append (stage3AfterKemBoxEvents dh4?) deriveKeysEvents st,
    show stage3AfterKemBoxEvents dh4? ++ deriveKeysEvents = stage3OkEvents dh4? from rfl]
  have hdh4_opt : dh4? = stage3Dh4Opt X W kp be x.coins := hdh4_eq
  rw [hdh4_opt]
  exact hnext s4 dk hdr kemCtBytes hkSlotBytes kemCtPtr' hs4

theorem stage3_all_okEvents_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {InitStateEnv : Params → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {st0 st : M.σ} {be : PreKeyBundleFields} {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)} {pqspkPtr : BitVec 64} {opkId : BitVec 32}
    {stk : Nat} {s0 s3 : State}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hCoins : ∀ {cStk : Nat}, cliCoinsFillStack ≤ cStk → cStk ≤ 2 ^ 63 →
      subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 618)
        (withLsCodeRoLoaded lsmpl (coinsFillSpecPlacedW3 cStk)))
    (hLocal : InitLocalCalleesPlaced A lim InitStateEnv mmpl gh W stk)
    (hFit : FitsEvents M lim st (stage3OkEvents (stage3Dh4Opt X W kp be x.coins)))
    (hEnv_dh1 :
      (let P := modelPrims X ⟨W.C, W.Q⟩
       let inp := initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)
       P.x25519 inp.ikASk inp.bundle.spkB = List.replicate 32 0) →
      ∃ evs, InitEnv x evs ∧ M.stepEvents stage3Dh1UnwindEvents st = M.stepEvents evs st0)
    (hEnv_dh2 :
      (let P := modelPrims X ⟨W.C, W.Q⟩
       let inp := initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)
       P.x25519 inp.ekASk inp.bundle.ikB = List.replicate 32 0) →
      ∃ evs, InitEnv x evs ∧ M.stepEvents stage3Dh2UnwindEvents st = M.stepEvents evs st0)
    (hEnv_dh3 :
      (let P := modelPrims X ⟨W.C, W.Q⟩
       let inp := initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)
       P.x25519 inp.ekASk inp.bundle.spkB = List.replicate 32 0) →
      ∃ evs, InitEnv x evs ∧ M.stepEvents stage3Dh3UnwindEvents st = M.stepEvents evs st0)
    (hEnv_dh4 :
      (let P := modelPrims X ⟨W.C, W.Q⟩
       let inp := initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)
       SignalPqxdh.dhOptNonZero (inp.bundle.opkB?.map fun (_, opkPk) => P.x25519 inp.ekASk opkPk) =
         false) →
      ∃ evs, InitEnv x evs ∧ M.stepEvents stage3Dh4UnwindEvents st = M.stepEvents evs st0)
    (hS : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (hcoinsLt : x.coins.length < 2 ^ 63)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hs3 : AtStage3Placed W X x be kp ekASk ekAPk pqspkPtr opkId s0 s3)
    (hpost : ∀ sf Pf, InitExitPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Q sf Pf)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf)
    (hnext : ∀ (s4 : State) (dk : SignalPqxdh.DRKey) (hdr : SignalPqxdh.HandshakeHdr)
        (kemCtBytes hkSlotBytes : List (BitVec 8)) (kemCtPtr : BitVec 64),
      AtStage4Placed W X x be kp ekASk ekAPk dk hdr kemCtBytes hkSlotBytes pqspkPtr kemCtPtr opkId
        s0 s4 →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s4
        (stage4MemPlaced A lim
          (M.stepEvents (stage3OkEvents (stage3Dh4Opt X W kp be x.coins)) st)
          x kp ekASk ekAPk kemCtBytes hkSlotBytes pqspkPtr kemCtPtr opkId stk s0 s4)
        Q Qp oom) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s3
      (stage3MemPlaced A lim st x kp ekASk ekAPk pqspkPtr opkId stk s0 s3) Q Qp oom := by
  obtain ⟨hFit192, hFitDh1, hFitDh2, hFitDh3, hFitDh4, hFitKemBox⟩ :=
    fitsEvents_stage3_of_okEvents hs3 hFit
  exact stage3_all_placed_ok hh @hCoins hLocal
    hFit192 hFitDh1 hFitDh2 hFitDh3 hFitDh4 hFitKemBox
    hEnv_dh1 hEnv_dh2 hEnv_dh3 hEnv_dh4 hS hcoinsLt hstk hstk64 hs3 hpost hpanic hnext

/-- Full Stage 3 composition (`+0x0760 → +0x10a4`) discharging coin-fill and DH/KEM hooks from
`RunHooksPlaced` and Block `59` from `SubsetA4InitCalleesPlaced`. -/
theorem stage3_all_a4_hooks_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {InitStateEnv : Params → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {st0 st : M.σ} {be : PreKeyBundleFields} {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)} {pqspkPtr : BitVec 64} {opkId : BitVec 32}
    {stk : Nat} {s0 s3 : State}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (ha4 : SubsetA4InitCalleesPlaced A lim InitStateEnv mmpl gh W)
    (hFit192 : FitsEvents M lim st (rustAllocEvents 192 1))
    (hFitDh1 : FitsEvents M lim (M.stepEvents (rustAllocEvents 192 1) st)
      (s3CalcAgreeEvents X W (toU8 kp.privateKey.bytes.toList)
        (toU8 x.bundle.spk.bytes.toList)))
    (hFitDh2 : FitsEvents M lim (M.stepEvents stage3AfterDh1Events st)
      (s3CalcAgreeEvents X W (toU8 ekASk) (toU8 x.bundle.idKey.publicKey.bytes.toList)))
    (hFitDh3 : FitsEvents M lim (M.stepEvents stage3AfterDh2Events st)
      (s3CalcAgreeEvents X W (toU8 ekASk) (toU8 x.bundle.spk.bytes.toList)))
    (hFitDh4 : FitsEvents M lim (M.stepEvents stage3AfterDh3Events st)
      (s3Dh4CalcAgreeEvents X W ekASk x.bundle.opk))
    (hFitKemBox : FitsEvents M lim
      (M.stepEvents (stage3AfterDh4Events (stage3Dh4Opt X W kp be x.coins)) st)
      deriveKeysAAllocPrefixEvents)
    (hEnv_dh1 :
      (let P := modelPrims X ⟨W.C, W.Q⟩
       let inp := initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)
       P.x25519 inp.ikASk inp.bundle.spkB = List.replicate 32 0) →
      ∃ evs, InitEnv x evs ∧ M.stepEvents stage3Dh1UnwindEvents st = M.stepEvents evs st0)
    (hEnv_dh2 :
      (let P := modelPrims X ⟨W.C, W.Q⟩
       let inp := initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)
       P.x25519 inp.ekASk inp.bundle.ikB = List.replicate 32 0) →
      ∃ evs, InitEnv x evs ∧ M.stepEvents stage3Dh2UnwindEvents st = M.stepEvents evs st0)
    (hEnv_dh3 :
      (let P := modelPrims X ⟨W.C, W.Q⟩
       let inp := initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)
       P.x25519 inp.ekASk inp.bundle.spkB = List.replicate 32 0) →
      ∃ evs, InitEnv x evs ∧ M.stepEvents stage3Dh3UnwindEvents st = M.stepEvents evs st0)
    (hEnv_dh4 :
      (let P := modelPrims X ⟨W.C, W.Q⟩
       let inp := initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)
       SignalPqxdh.dhOptNonZero (inp.bundle.opkB?.map fun (_, opkPk) => P.x25519 inp.ekASk opkPk) =
         false) →
      ∃ evs, InitEnv x evs ∧ M.stepEvents stage3Dh4UnwindEvents st = M.stepEvents evs st0)
    (hS : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (hcoinsLt : x.coins.length < 2 ^ 63)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hs3 : AtStage3Placed W X x be kp ekASk ekAPk pqspkPtr opkId s0 s3)
    (hpost : ∀ sf Pf, InitExitPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Q sf Pf)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf)
    (hnext : ∀ (s4 : State) (dk : SignalPqxdh.DRKey) (hdr : SignalPqxdh.HandshakeHdr)
        (kemCtBytes hkSlotBytes : List (BitVec 8)) (kemCtPtr : BitVec 64),
      AtStage4Placed W X x be kp ekASk ekAPk dk hdr kemCtBytes hkSlotBytes pqspkPtr kemCtPtr opkId
        s0 s4 →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s4
        (stage4MemPlaced A lim
          (M.stepEvents (stage3OkEvents (stage3Dh4Opt X W kp be x.coins)) st)
          x kp ekASk ekAPk kemCtBytes hkSlotBytes pqspkPtr kemCtPtr opkId stk s0 s4)
        Q Qp oom) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s3
      (stage3MemPlaced A lim st x kp ekASk ekAPk pqspkPtr opkId stk s0 s3) Q Qp oom := by
  refine dh1_step_hooks_placed_ok hh hS hstk hstk64 hs3 hFit192 hFitDh1 hEnv_dh1 hpost hpanic
    fun s_a secretsPtr dh1 hdh1_eq hdh1_nz hsecNonNull hc_a htr_a
      hx20_a hx21_a hx22_a hx24_a hx25_a hx26_a => ?_
  have hdh1_len : dh1.length = 32 := hdh1_eq ▸ modelPrims_x25519_len X ⟨W.C, W.Q⟩ _ _
  refine dh2_step_hooks_placed_ok hh hS hstk hstk64 hs3 hFitDh2
    (fun h0 =>
      let ⟨evs, hev, hst⟩ := hEnv_dh2 h0
      ⟨evs, hev, (M.stepEvents_append stage3AfterDh1Events unwind1548Events st).symm.trans hst⟩)
    hpost hpanic hdh1_len hsecNonNull hc_a htr_a hx20_a hx21_a hx22_a hx24_a hx25_a hx26_a
    fun s_b dh2 hdh2_eq hdh2_nz hc_b htr_b hx20_b hx21_b hx22_b hx24_b hx26_b => ?_
  rw [show dh1OkEvents = stage3AfterDh1Events from rfl,
    ← M.stepEvents_append stage3AfterDh1Events dh2OkEvents st,
    show stage3AfterDh1Events ++ dh2OkEvents = stage3AfterDh2Events from rfl]
  have hdh2_len : dh2.length = 32 := hdh2_eq ▸ modelPrims_x25519_len X ⟨W.C, W.Q⟩ _ _
  refine dh3_step_hooks_placed_ok hh hFitDh3
    (fun h0 =>
      let ⟨evs, hev, hst⟩ := hEnv_dh3 h0
      ⟨evs, hev,
        (stepEvents_unwind1548Events M (M.stepEvents stage3AfterDh2Events st)).trans
          ((M.stepEvents_append stage3AfterDh2Events unwind1548Events st).symm.trans hst)⟩)
    hS hstk hstk64 hs3 hpost hpanic hdh1_len hdh2_len hsecNonNull hc_b htr_b
    hx20_b hx21_b hx22_b hx24_b hx26_b
    fun s_c dh3 hdh3_eq hdh3_nz hc_c htr_c hx20_c hx21_c hx22_c hx26_c => ?_
  rw [← M.stepEvents_append stage3AfterDh2Events dh3StepOkEvents st,
    show stage3AfterDh2Events ++ dh3StepOkEvents = stage3AfterDh3Events from rfl]
  have hdh3_len : dh3.length = 32 := hdh3_eq ▸ modelPrims_x25519_len X ⟨W.C, W.Q⟩ _ _
  refine dh4_step_hooks_placed_ok hh hFitDh4
    (fun h0 =>
      let ⟨evs, hev, hst⟩ := hEnv_dh4 h0
      ⟨evs, hev,
        (stepEvents_unwind1548Events M (M.stepEvents stage3AfterDh3Events st)).trans
          ((M.stepEvents_append stage3AfterDh3Events unwind1548Events st).symm.trans hst)⟩)
    hS hstk hstk64 hs3 hpost hpanic hdh1_len hdh2_len hdh3_len hsecNonNull hc_c htr_c
    hx20_c hx21_c hx22_c hx26_c
    fun s_d dh4? hdh4_eq hdh4_nz hdh4_len hc_d htr_d hx20_d hx21_d hx22_d => ?_
  rw [← M.stepEvents_append stage3AfterDh3Events (dh4OptEvents dh4?) st,
    show stage3AfterDh3Events ++ dh4OptEvents dh4? = stage3AfterDh4Events dh4? from rfl]
  refine kem_coins_a_hooks_placed_ok hh hcoinsLt hstk hstk64 hs3
    hc_d htr_d hx20_d hx21_d hx22_d hpanic
    fun s_e z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23
      hc_e htr_e hx20_e hx21_e => ?_
  refine kem_coins_b_hooks_placed_ok hh hcoinsLt hpanic hc_e htr_e hx20_e hx21_e
    fun s_f hc_f htr_f hx20_f hx21_f => ?_
  refine kem_coins_c_hooks_placed_ok hh hcoinsLt hpanic hc_f htr_f hx20_f hx21_f
    fun s_g hc_g htr_g hx20_g hx21_g hx25_g hx22_g hx26_g hx23_g hx27_g hx28_g hx24_g => ?_
  refine kem_encaps_hooks_placed_ok hh hstk hstk64 hs3 hpanic hc_g htr_g
    hx20_g hx21_g hx25_g hx22_g hx26_g hx23_g hx27_g hx28_g hx24_g
    fun s_h hc_h htr_h hx20_h hx21_h => ?_
  have hFitKemBox' :
      FitsEvents M lim (M.stepEvents (stage3AfterDh4Events dh4?) st)
        deriveKeysAAllocPrefixEvents := by
    simpa only [stage3Dh4Opt, ← hdh4_eq] using hFitKemBox
  refine derive_keys_a_hooks_placed_ok hh hFitKemBox' hpanic hc_h htr_h hx20_h hx21_h
    fun s_i ssBoxPtr kemCtPtr hkemNonNull hc_i htr_i hx20_i hx21_i hx26_i => ?_
  rw [← M.stepEvents_append (stage3AfterDh4Events dh4?) deriveKeysAEvents st,
    show stage3AfterDh4Events dh4? ++ deriveKeysAEvents = stage3AfterKemBoxEvents dh4? from rfl]
  refine derive_keys_a4_placed_ok hh ha4 hstk hstk64 hs3 hpanic
    hdh1_eq hdh1_nz hdh1_len hdh2_eq hdh2_nz hdh2_len hdh3_eq hdh3_nz hdh3_len
    hdh4_eq hdh4_nz hdh4_len hkemNonNull hc_i htr_i hx20_i hx21_i hx26_i
    fun s4 dk hdr kemCtBytes hkSlotBytes kemCtPtr' hs4 => ?_
  rw [← M.stepEvents_append (stage3AfterKemBoxEvents dh4?) deriveKeysEvents st,
    show stage3AfterKemBoxEvents dh4? ++ deriveKeysEvents = stage3OkEvents dh4? from rfl]
  have hdh4_opt : dh4? = stage3Dh4Opt X W kp be x.coins := hdh4_eq
  rw [hdh4_opt]
  exact hnext s4 dk hdr kemCtBytes hkSlotBytes kemCtPtr' hs4

theorem stage3_all_no_coins_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {InitStateEnv : Params → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {st0 st : M.σ} {be : PreKeyBundleFields} {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)} {pqspkPtr : BitVec 64} {opkId : BitVec 32}
    {stk : Nat} {s0 s3 : State}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hLocal : InitLocalCalleesPlaced A lim InitStateEnv mmpl gh W stk)
    (hFit192 : FitsEvents M lim st (rustAllocEvents 192 1))
    (hFitDh1 : FitsEvents M lim (M.stepEvents (rustAllocEvents 192 1) st)
      (s3CalcAgreeEvents X W (toU8 kp.privateKey.bytes.toList)
        (toU8 x.bundle.spk.bytes.toList)))
    (hFitDh2 : FitsEvents M lim (M.stepEvents stage3AfterDh1Events st)
      (s3CalcAgreeEvents X W (toU8 ekASk) (toU8 x.bundle.idKey.publicKey.bytes.toList)))
    (hFitDh3 : FitsEvents M lim (M.stepEvents stage3AfterDh2Events st)
      (s3CalcAgreeEvents X W (toU8 ekASk) (toU8 x.bundle.spk.bytes.toList)))
    (hFitDh4 : FitsEvents M lim (M.stepEvents stage3AfterDh3Events st)
      (s3Dh4CalcAgreeEvents X W ekASk x.bundle.opk))
    (hFitKemBox : FitsEvents M lim
      (M.stepEvents (stage3AfterDh4Events (stage3Dh4Opt X W kp be x.coins)) st)
      deriveKeysAEvents)
    (hEnv_dh1 :
      (let P := modelPrims X ⟨W.C, W.Q⟩
       let inp := initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)
       P.x25519 inp.ikASk inp.bundle.spkB = List.replicate 32 0) →
      ∃ evs, InitEnv x evs ∧ M.stepEvents stage3Dh1UnwindEvents st = M.stepEvents evs st0)
    (hEnv_dh2 :
      (let P := modelPrims X ⟨W.C, W.Q⟩
       let inp := initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)
       P.x25519 inp.ekASk inp.bundle.ikB = List.replicate 32 0) →
      ∃ evs, InitEnv x evs ∧ M.stepEvents stage3Dh2UnwindEvents st = M.stepEvents evs st0)
    (hEnv_dh3 :
      (let P := modelPrims X ⟨W.C, W.Q⟩
       let inp := initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)
       P.x25519 inp.ekASk inp.bundle.spkB = List.replicate 32 0) →
      ∃ evs, InitEnv x evs ∧ M.stepEvents stage3Dh3UnwindEvents st = M.stepEvents evs st0)
    (hEnv_dh4 :
      (let P := modelPrims X ⟨W.C, W.Q⟩
       let inp := initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)
       SignalPqxdh.dhOptNonZero (inp.bundle.opkB?.map fun (_, opkPk) => P.x25519 inp.ekASk opkPk) =
         false) →
      ∃ evs, InitEnv x evs ∧ M.stepEvents stage3Dh4UnwindEvents st = M.stepEvents evs st0)
    (hS : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (hcoinsLt : x.coins.length < 2 ^ 63)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hs3 : AtStage3Placed W X x be kp ekASk ekAPk pqspkPtr opkId s0 s3)
    (hpost : ∀ sf Pf, InitExitPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Q sf Pf)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf)
    (hnext : ∀ (s4 : State) (dk : SignalPqxdh.DRKey) (hdr : SignalPqxdh.HandshakeHdr)
        (kemCtBytes hkSlotBytes : List (BitVec 8)) (kemCtPtr : BitVec 64),
      AtStage4Placed W X x be kp ekASk ekAPk dk hdr kemCtBytes hkSlotBytes pqspkPtr kemCtPtr opkId
        s0 s4 →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s4
        (stage4MemPlaced A lim
          (M.stepEvents (stage3OkEvents (stage3Dh4Opt X W kp be x.coins)) st)
          x kp ekASk ekAPk kemCtBytes hkSlotBytes pqspkPtr kemCtPtr opkId stk s0 s4)
        Q Qp oom) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s3
      (stage3MemPlaced A lim st x kp ekASk ekAPk pqspkPtr opkId stk s0 s3) Q Qp oom := by
  refine dh1_step_placed_ok hh hLocal hS hstk hstk64 hs3 hFit192 hFitDh1 hEnv_dh1 hpost hpanic
    fun s_a secretsPtr dh1 hdh1_eq hdh1_nz hsecNonNull hc_a htr_a
      hx20_a hx21_a hx22_a hx24_a hx25_a hx26_a => ?_
  have hdh1_len : dh1.length = 32 := hdh1_eq ▸ modelPrims_x25519_len X ⟨W.C, W.Q⟩ _ _
  refine dh2_step_placed_ok hh hLocal hS hstk hstk64 hs3 hFitDh2
    (fun h0 =>
      let ⟨evs, hev, hst⟩ := hEnv_dh2 h0
      ⟨evs, hev, (M.stepEvents_append stage3AfterDh1Events unwind1548Events st).symm.trans hst⟩)
    hpost hpanic hdh1_len hsecNonNull hc_a htr_a hx20_a hx21_a hx22_a hx24_a hx25_a hx26_a
    fun s_b dh2 hdh2_eq hdh2_nz hc_b htr_b hx20_b hx21_b hx22_b hx24_b hx26_b => ?_
  rw [show dh1OkEvents = stage3AfterDh1Events from rfl,
    ← M.stepEvents_append stage3AfterDh1Events dh2OkEvents st,
    show stage3AfterDh1Events ++ dh2OkEvents = stage3AfterDh2Events from rfl]
  have hdh2_len : dh2.length = 32 := hdh2_eq ▸ modelPrims_x25519_len X ⟨W.C, W.Q⟩ _ _
  refine dh3_step_placed_ok hh hLocal hFitDh3
    (fun h0 =>
      let ⟨evs, hev, hst⟩ := hEnv_dh3 h0
      ⟨evs, hev,
        (stepEvents_unwind1548Events M (M.stepEvents stage3AfterDh2Events st)).trans
          ((M.stepEvents_append stage3AfterDh2Events unwind1548Events st).symm.trans hst)⟩)
    hS hstk hstk64 hs3 hpost hpanic hdh1_len hdh2_len hsecNonNull hc_b htr_b
    hx20_b hx21_b hx22_b hx24_b hx26_b
    fun s_c dh3 hdh3_eq hdh3_nz hc_c htr_c hx20_c hx21_c hx22_c hx26_c => ?_
  rw [← M.stepEvents_append stage3AfterDh2Events dh3StepOkEvents st,
    show stage3AfterDh2Events ++ dh3StepOkEvents = stage3AfterDh3Events from rfl]
  have hdh3_len : dh3.length = 32 := hdh3_eq ▸ modelPrims_x25519_len X ⟨W.C, W.Q⟩ _ _
  refine dh4_step_placed_ok hh hLocal hFitDh4
    (fun h0 =>
      let ⟨evs, hev, hst⟩ := hEnv_dh4 h0
      ⟨evs, hev,
        (stepEvents_unwind1548Events M (M.stepEvents stage3AfterDh3Events st)).trans
          ((M.stepEvents_append stage3AfterDh3Events unwind1548Events st).symm.trans hst)⟩)
    hS hstk hstk64 hs3 hpost hpanic hdh1_len hdh2_len hdh3_len hsecNonNull hc_c htr_c
    hx20_c hx21_c hx22_c hx26_c
    fun s_d dh4? hdh4_eq hdh4_nz hdh4_len hc_d htr_d hx20_d hx21_d hx22_d => ?_
  rw [← M.stepEvents_append stage3AfterDh3Events (dh4OptEvents dh4?) st,
    show stage3AfterDh3Events ++ dh4OptEvents dh4? = stage3AfterDh4Events dh4? from rfl]
  refine kem_coins_a_hooks_placed_ok hh hcoinsLt hstk hstk64 hs3
    hc_d htr_d hx20_d hx21_d hx22_d hpanic
    fun s_e z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23
      hc_e htr_e hx20_e hx21_e => ?_
  refine kem_coins_b_hooks_placed_ok hh hcoinsLt hpanic hc_e htr_e hx20_e hx21_e
    fun s_f hc_f htr_f hx20_f hx21_f => ?_
  refine kem_coins_c_hooks_placed_ok hh hcoinsLt hpanic hc_f htr_f hx20_f hx21_f
    fun s_g hc_g htr_g hx20_g hx21_g hx25_g hx22_g hx26_g hx23_g hx27_g hx28_g hx24_g => ?_
  refine kem_encaps_hooks_placed_ok hh hstk hstk64 hs3 hpanic hc_g htr_g
    hx20_g hx21_g hx25_g hx22_g hx26_g hx23_g hx27_g hx28_g hx24_g
    fun s_h hc_h htr_h hx20_h hx21_h => ?_
  have hFitKemBox' :
      FitsEvents M lim (M.stepEvents (stage3AfterDh4Events dh4?) st) deriveKeysAEvents := by
    simpa only [stage3Dh4Opt, ← hdh4_eq] using hFitKemBox
  refine derive_keys_a_placed_ok hh hLocal hFitKemBox' hpanic hc_h htr_h hx20_h hx21_h
    fun s_i ssBoxPtr kemCtPtr hkemNonNull hc_i htr_i hx20_i hx21_i hx26_i => ?_
  rw [← M.stepEvents_append (stage3AfterDh4Events dh4?) deriveKeysAEvents st,
    show stage3AfterDh4Events dh4? ++ deriveKeysAEvents = stage3AfterKemBoxEvents dh4? from rfl]
  refine derive_keys_placed_ok hh hLocal hstk hstk64 hs3 hpanic
    hdh1_eq hdh1_nz hdh1_len hdh2_eq hdh2_nz hdh2_len hdh3_eq hdh3_nz hdh3_len
    hdh4_eq hdh4_nz hdh4_len hkemNonNull hc_i htr_i hx20_i hx21_i hx26_i
    fun s4 dk hdr kemCtBytes hkSlotBytes kemCtPtr' hs4 => ?_
  rw [← M.stepEvents_append (stage3AfterKemBoxEvents dh4?) deriveKeysEvents st,
    show stage3AfterKemBoxEvents dh4? ++ deriveKeysEvents = stage3OkEvents dh4? from rfl]
  have hdh4_opt : dh4? = stage3Dh4Opt X W kp be x.coins := hdh4_eq
  rw [hdh4_opt]
  exact hnext s4 dk hdr kemCtBytes hkSlotBytes kemCtPtr' hs4

theorem stage3_all_okEvents_a4_hooks_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {InitStateEnv : Params → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {st0 st : M.σ} {be : PreKeyBundleFields} {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)} {pqspkPtr : BitVec 64} {opkId : BitVec 32}
    {stk : Nat} {s0 s3 : State}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (ha4 : SubsetA4InitCalleesPlaced A lim InitStateEnv mmpl gh W)
    (hFit : FitsEvents M lim st (stage3OkEvents (stage3Dh4Opt X W kp be x.coins)))
    (hEnv_dh1 :
      (let P := modelPrims X ⟨W.C, W.Q⟩
       let inp := initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)
       P.x25519 inp.ikASk inp.bundle.spkB = List.replicate 32 0) →
      ∃ evs, InitEnv x evs ∧ M.stepEvents stage3Dh1UnwindEvents st = M.stepEvents evs st0)
    (hEnv_dh2 :
      (let P := modelPrims X ⟨W.C, W.Q⟩
       let inp := initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)
       P.x25519 inp.ekASk inp.bundle.ikB = List.replicate 32 0) →
      ∃ evs, InitEnv x evs ∧ M.stepEvents stage3Dh2UnwindEvents st = M.stepEvents evs st0)
    (hEnv_dh3 :
      (let P := modelPrims X ⟨W.C, W.Q⟩
       let inp := initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)
       P.x25519 inp.ekASk inp.bundle.spkB = List.replicate 32 0) →
      ∃ evs, InitEnv x evs ∧ M.stepEvents stage3Dh3UnwindEvents st = M.stepEvents evs st0)
    (hEnv_dh4 :
      (let P := modelPrims X ⟨W.C, W.Q⟩
       let inp := initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)
       SignalPqxdh.dhOptNonZero (inp.bundle.opkB?.map fun (_, opkPk) => P.x25519 inp.ekASk opkPk) =
         false) →
      ∃ evs, InitEnv x evs ∧ M.stepEvents stage3Dh4UnwindEvents st = M.stepEvents evs st0)
    (hS : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (hcoinsLt : x.coins.length < 2 ^ 63)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hs3 : AtStage3Placed W X x be kp ekASk ekAPk pqspkPtr opkId s0 s3)
    (hpost : ∀ sf Pf, InitExitPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Q sf Pf)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf)
    (hnext : ∀ (s4 : State) (dk : SignalPqxdh.DRKey) (hdr : SignalPqxdh.HandshakeHdr)
        (kemCtBytes hkSlotBytes : List (BitVec 8)) (kemCtPtr : BitVec 64),
      AtStage4Placed W X x be kp ekASk ekAPk dk hdr kemCtBytes hkSlotBytes pqspkPtr kemCtPtr opkId
        s0 s4 →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s4
        (stage4MemPlaced A lim
          (M.stepEvents (stage3OkEvents (stage3Dh4Opt X W kp be x.coins)) st)
          x kp ekASk ekAPk kemCtBytes hkSlotBytes pqspkPtr kemCtPtr opkId stk s0 s4)
        Q Qp oom) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s3
      (stage3MemPlaced A lim st x kp ekASk ekAPk pqspkPtr opkId stk s0 s3) Q Qp oom := by
  obtain ⟨hFit192, hFitDh1, hFitDh2, hFitDh3, hFitDh4, hFitKemBox⟩ :=
    fitsEvents_stage3_of_okEvents hs3 hFit
  exact stage3_all_a4_hooks_placed_ok hh ha4
    hFit192 hFitDh1 hFitDh2 hFitDh3 hFitDh4
    (fitsEvents_deriveKeysAAllocPrefix_of_full hFitKemBox)
    hEnv_dh1 hEnv_dh2 hEnv_dh3 hEnv_dh4 hS hcoinsLt hstk hstk64 hs3 hpost hpanic hnext

theorem stage3_all_okEvents_evs_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {InitStateEnv : Params → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {st0 : M.σ} {evs_pre : List AllocEvent}
    {be : PreKeyBundleFields} {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)} {pqspkPtr : BitVec 64} {opkId : BitVec 32}
    {stk : Nat} {s0 s3 : State}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hCoins : ∀ {cStk : Nat}, cliCoinsFillStack ≤ cStk → cStk ≤ 2 ^ 63 →
      subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 618)
        (withLsCodeRoLoaded lsmpl (coinsFillSpecPlacedW3 cStk)))
    (hLocal : InitLocalCalleesPlaced A lim InitStateEnv mmpl gh W stk)
    (hFit : FitsEvents M lim (M.stepEvents evs_pre st0)
      (stage3OkEvents (stage3Dh4Opt X W kp be x.coins)))
    (hEnv_dh1 :
      (let P := modelPrims X ⟨W.C, W.Q⟩
       let inp := initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)
       P.x25519 inp.ikASk inp.bundle.spkB = List.replicate 32 0) →
      InitEnv x (evs_pre ++ stage3Dh1UnwindEvents))
    (hEnv_dh2 :
      (let P := modelPrims X ⟨W.C, W.Q⟩
       let inp := initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)
       P.x25519 inp.ekASk inp.bundle.ikB = List.replicate 32 0) →
      InitEnv x (evs_pre ++ stage3Dh2UnwindEvents))
    (hEnv_dh3 :
      (let P := modelPrims X ⟨W.C, W.Q⟩
       let inp := initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)
       P.x25519 inp.ekASk inp.bundle.spkB = List.replicate 32 0) →
      InitEnv x (evs_pre ++ stage3Dh3UnwindEvents))
    (hEnv_dh4 :
      (let P := modelPrims X ⟨W.C, W.Q⟩
       let inp := initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)
       SignalPqxdh.dhOptNonZero (inp.bundle.opkB?.map fun (_, opkPk) => P.x25519 inp.ekASk opkPk) =
         false) →
      InitEnv x (evs_pre ++ stage3Dh4UnwindEvents))
    (hS : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (hcoinsLt : x.coins.length < 2 ^ 63)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hs3 : AtStage3Placed W X x be kp ekASk ekAPk pqspkPtr opkId s0 s3)
    (hpost : ∀ sf Pf, InitExitPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Q sf Pf)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf)
    (hnext : ∀ (s4 : State) (dk : SignalPqxdh.DRKey) (hdr : SignalPqxdh.HandshakeHdr)
        (kemCtBytes hkSlotBytes : List (BitVec 8)) (kemCtPtr : BitVec 64),
      AtStage4Placed W X x be kp ekASk ekAPk dk hdr kemCtBytes hkSlotBytes pqspkPtr kemCtPtr opkId
        s0 s4 →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s4
        (stage4MemPlaced A lim
          (M.stepEvents (evs_pre ++ stage3OkEvents (stage3Dh4Opt X W kp be x.coins)) st0)
          x kp ekASk ekAPk kemCtBytes hkSlotBytes pqspkPtr kemCtPtr opkId stk s0 s4)
        Q Qp oom) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s3
      (stage3MemPlaced A lim (M.stepEvents evs_pre st0) x kp ekASk ekAPk pqspkPtr opkId stk s0 s3)
      Q Qp oom := by
  refine stage3_all_okEvents_placed_ok hh @hCoins hLocal hFit
    (fun h0 => ⟨evs_pre ++ stage3Dh1UnwindEvents, hEnv_dh1 h0,
      (M.stepEvents_append evs_pre stage3Dh1UnwindEvents st0).symm⟩)
    (fun h0 => ⟨evs_pre ++ stage3Dh2UnwindEvents, hEnv_dh2 h0,
      (M.stepEvents_append evs_pre stage3Dh2UnwindEvents st0).symm⟩)
    (fun h0 => ⟨evs_pre ++ stage3Dh3UnwindEvents, hEnv_dh3 h0,
      (M.stepEvents_append evs_pre stage3Dh3UnwindEvents st0).symm⟩)
    (fun h0 => ⟨evs_pre ++ stage3Dh4UnwindEvents, hEnv_dh4 h0,
      (M.stepEvents_append evs_pre stage3Dh4UnwindEvents st0).symm⟩)
    hS hcoinsLt hstk hstk64 hs3 hpost hpanic
    fun s4 dk hdr kemCtBytes hkSlotBytes kemCtPtr hs4 => ?_
  rw [← M.stepEvents_append evs_pre (stage3OkEvents (stage3Dh4Opt X W kp be x.coins)) st0]
  exact hnext s4 dk hdr kemCtBytes hkSlotBytes kemCtPtr hs4

end

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.DeriveKeysPlacedBudget
