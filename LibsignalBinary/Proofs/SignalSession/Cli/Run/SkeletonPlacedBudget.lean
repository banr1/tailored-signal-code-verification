/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.RustStdAllocBudgetBridge
public import LibsignalBinary.Proofs.RecordCodecs.DepsBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AddressPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AllocFsSitesPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Reserve11PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.TryAllocateIn3PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Concat2PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropPreKeyMsgPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropSignalMessagePlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropSpeOwnedPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropStoresPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFromPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.SigTryFromPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
public import LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostRkSomeBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Budget-Threaded Callee Slots and Hook Bundles for `signal_session::run` (Placed)

Budget-pool counterparts of `RunHooksPlaced`, `RunCalleesEnvs`, `RunCalleesPlaced`, and cross-block
(`i < 619`) callee transfer lemmas for Block `579` (`signal_session::run`) under
`[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget

open Arm64 Arm64.Process ProofLib SepProp
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement blkPC_201 blkPl_201 instIsLsBlockProg_201
   libsignalMutatedBlocks ls_hook_ok_ultra_of_mem lsmpl lsρ)
open CryptoVerification.E2E.Record.Placed (blkPl_85)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (FsFiles TraceFsSound ls_subroutine_ok_rocl_of_block subroutine_ok_rocl_of_plain
   subroutine_ok_withLsCodeRoLoaded_of_plain subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
   withLsCodeRoLoaded withLsRoCl)
open CryptoVerification.LibsignalTripleRatchet
  (TryFromGhost doReserveStackX extHookStack finishGrowStackX lsMemcpySym)
open CryptoVerification.LibsignalTripleRatchet.Getters (dropSpeStackX)
open CryptoVerification.LibsignalTripleRatchet.Wire (deserializeFullPlacedSpec)
open CryptoVerification.LibsignalTripleRatchetRepr (uuidTryParse)
open CryptoVerification.RecordCodecs.Placed (blkPC_18 blkPl_18 instIsLsBlockProg_18)
open CryptoVerification.RecordCodecsBinary.IdentityKeyDecode (identityKey_decode_placed_ok)
open CryptoVerification.SignalSession
  (CliHooks cliExternsPlaced lsFormatInnerSym lsFromUtf8Sym lsMemrchrSym lsReadFileSym
   lsRustAllocZeroedSymCli lsStringCloneSym)
open CryptoVerification.SignalSession.Cli (DirGhost cliBcmpSpec)
open CryptoVerification.SignalSession.Cli.MainHops (cliIo cliWrOk fromUtf8AsciiSpec memrchrSpec)
open CryptoVerification.SignalSession.Cli.Placed
  (blkPl_550 blkPl_553 blkPl_554 blkPl_555 blkPl_590 blkPl_596 blkPl_598
   lsProg_580 lsProg_588 lsProg_596)
open CryptoVerification.SignalSession.Cli.Run.Placed (lsProg_579)
open CryptoVerification.SignalSession.Cli.RunGlue
  (CliGhostHooks FsTHooks IsFsC cliGhostExterns cliGhostExterns_allocZeroed
   cliGhostExterns_other cliGhostExterns_panic_of_mem fsTHooks_cliExternsPlaced hookSat_of_eq
   traceFsSound_lsProg_cli)
open CryptoVerification.SignalSession.Cli.RunSkeleton
  (CalleeSlot.OkPlaced RunBudgets RunSlots pathNeed splitIdNeed splitSignedNeed)
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon
  (CliPanicHooksPlaced cliPanicHooksPlaced_cli)
open CryptoVerification.SpqrV1.Alloc (sessionMemcpyRegionROSpec)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget rustCliAllocBudgetSpec)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (stringCloneBudgetSpec)
open LibsignalBinary.Heap.SpecBudget (formatInnerBudgetSpec withVmPreserved)
open LibsignalBinary.Proofs.RecordCodecs.DepsBudget (CodecHooksPlaced identityKeyDecodeRawSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudget
  (PathEnv path_placed_caller_ok_of_deps)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.CalleesBudget (addressSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AddressPlacedBudget
  (address_placed_ok_rocl)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AllocFsSitesPlacedBudget
  (AllocContractsFsPlaced.shim2_rocl)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Reserve11PlacedBudget
  (allocNoOomExtern_fs_rocl cliDoReserve_placed_ok_at)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.TryAllocateIn3PlacedBudget
  (tryAllocateIn3_placed_okFs_of_hooks_at tryAllocateInRustSpecOf)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Concat2PlacedBudget
  (cliConcat2SpecPlaced cliConcat2_placed_at_block)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropPreKeyMsgPlacedBudget
  (cliDropPreKeyMsg_placed_at_block dropPreKeyMsgSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropSignalMessagePlacedBudget
  (cliDropSignalMessage_placed_at_block dropSignalMessageSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropSpeOwnedPlacedBudget
  (DropSpeOwnedOkAtBlock cliDropSpeOwned_placed_at_block cliDropSpe_placed_at_block
   dropSpeSpecStkPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropStoresPlacedBudget
  (cliDropStores_placed_at_block dropStoresSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.SigTryFromPlacedBudget
  (SubsetA4SigTryFromPlaced cliSigTryFrom_placed_at_block tryFromSpecPlaced)
open CryptoVerification.SignalSession.Cli.Slots (cliGhostExterns_sat_of_cliExternsPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (BaseHelperRows allocContractsFsPlaced_of_ghost allocContractsXCliPlaced_of_ghost
   cliExternsPlaced_baseHelperRows cliGhostExterns_panics
   codecHooksPlaced_of_ghost traceFsSound_lsProg_ghost)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
  (CliAllocHooks CliGhostAllocHooks CliGhostSpqrAllocHooks allocContractsFsPlaced_of_hooks
   allocContractsXCliPlaced_of_hooks
   cliExternsPlaced_bcmp_budget_sat cliExternsPlaced_fromUtf8_budget_sat
   cliExternsPlaced_memrchr_budget_sat cliGhostExterns_memcpyRegionRO_budget_sat
   codecHooksPlaced_of_hooks)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsFsPlaced AllocContractsXCliPlaced bundleReadSpecPlaced dirGetSpecPlaced
   pathSpecPlaced readFileSpecPlaced splitIdSpecPlaced splitSignedSpecPlaced)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarintPlacedCommonBudget (doReserveSpecOf)
open LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget (dropSpeSpecX)
open LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostRkSomeBudget (deserializeFull_vm_placed_ok)

/-! ## Placed hook and callee bundles -/

/-- Budget-threaded `[LibsignalPlacement]` extern hook hypotheses for `signal_session::run` (Block `579`). -/
structure RunHooksPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ext : LibsignalHooks) : Prop where
  alloc : AllocContractsXCliPlaced A lim ext
  allocFs : AllocContractsFsPlaced A lim ext
  panics : CliPanicHooksPlaced ext
  memcpyRO : HookSat ext lsMemcpySym (withVmPreserved sessionMemcpyRegionROSpec)
  bcmp : HookSat ext "bcmp" (withVmPreserved cliBcmpSpec)
  fs : ∀ (prog : Program) (i : Nat), [IsLsBlockProg prog i ext] → TraceFsSound prog
  utf8 : ∀ stk : Nat, HookSat ext lsFromUtf8Sym (withVmPreserved (fromUtf8AsciiSpec stk))
  memrchr : ∀ stk : Nat, HookSat ext lsMemrchrSym (withVmPreserved (memrchrSpec stk))
  codecHooks : CodecHooksPlaced M A lim ext
  allocZeroed : HookSat ext lsRustAllocZeroedSymCli (rustCliAllocBudgetSpec M A lim true)
  stringClone : HookSat ext lsStringCloneSym (stringCloneBudgetSpec M A lim)
  formatInner : HookSat ext lsFormatInnerSym (formatInnerBudgetSpec M A lim)

/-- Allocation-event envelopes for the non-slot callees of `RunCalleesPlaced` (`read_file`,
`Dir::get`, `read_bundle::{closure#0}`, `split_id`, `split_signed`). -/
structure RunCalleesEnvs where
  readFile : FsFiles → List (BitVec 8) → List AllocEvent → Prop
  dirGet : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop
  bundleRead : FsFiles → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop
  splitId : List (BitVec 8) → List AllocEvent → Prop
  splitSigned : List (BitVec 8) → List AllocEvent → Prop

/-- Budget-threaded `[LibsignalPlacement]` callee contracts for `signal_session::run` (Block `579`, `lsProg_579 ext`). -/
structure RunCalleesPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (cEnvs : RunCalleesEnvs)
    (ext : LibsignalHooks) (B : RunBudgets) (σ : RunSlots) : Prop where
  /-- `read_file` at the stub (`lsReadFileSym`). -/
  readFile : subroutine_ok (lsProg_579 ext) (lsρ lsReadFileSym)
    (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile cEnvs.readFile)
  /-- `Dir::get` (`<signal_session::stores::Dir>::get`, Block `589`). -/
  dirGet : ∀ {stk : Nat}, B.dirGetNeed ≤ stk →
    subroutine_ok (lsProg_579 ext) (lsmpl.base 589)
      (dirGetSpecPlaced cliIo.rd cliWrOk A lim cEnvs.dirGet stk)
  /-- `read_bundle::{closure#0}` (Block `563`). -/
  bundleRead : ∀ {stk : Nat}, B.bundleReadNeed ≤ stk →
    subroutine_ok (lsProg_579 ext) (lsmpl.base 563)
      (bundleReadSpecPlaced cliIo.rd cliWrOk A lim cEnvs.bundleRead stk)
  /-- `split_id` (Block `593`). -/
  splitId : ∀ {stk : Nat}, splitIdNeed ≤ stk →
    subroutine_ok (lsProg_579 ext) (lsmpl.base 593)
      (splitIdSpecPlaced A lim cEnvs.splitId stk)
  /-- `split_signed` (Block `592`). -/
  splitSigned : ∀ {stk : Nat}, splitSignedNeed ≤ stk →
    subroutine_ok (lsProg_579 ext) (lsmpl.base 592)
      (splitSignedSpecPlaced A lim cEnvs.splitSigned stk)
  /-- `drop_glue<SPE> [local#4]` fixed-stack contract (Block `552`). -/
  dropSpeX : subroutine_ok (lsProg_579 ext) (blkPl_553).base
    (withLsCodeRoLoaded lsmpl (dropSpeSpecX M A lim))
  /-- `drop_glue<SPE> [local#4]` arbitrary-stack contract (Block `552`). -/
  dropSpe : ∀ (stk : Nat), 32 + extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    subroutine_ok (lsProg_579 ext) (blkPl_553).base
      (dropSpeSpecStkPlaced A lim stk)
  /-- `signal_session_ratchet::encrypt` (Block `464`). -/
  encrypt : σ.encrypt.OkPlaced (lsProg_579 ext) (lsmpl.base 464)
  /-- `signal_session_ratchet::decrypt_signal` (Block `463`). -/
  decryptSignal : σ.decryptSignal.OkPlaced (lsProg_579 ext) (lsmpl.base 463)
  /-- `signal_session_handshake::initiate` (Block `521`). -/
  initiate : σ.initiate.OkPlaced (lsProg_579 ext) (lsmpl.base 521)
  /-- `signal_session_handshake::decrypt_prekey` (Block `520`). -/
  decryptPrekey : σ.decryptPrekey.OkPlaced (lsProg_579 ext) (lsmpl.base 520)
  /-- `kem::Key<Public>::deserialize` (Block `590`). -/
  kemDeserialize : σ.kemDeserialize.OkPlaced (lsProg_579 ext) (blkPl_590).base

/-! ## Callees derived from `RunHooksPlaced` -/

/-- `core::str::converts::from_utf8` (`lsFromUtf8Sym`, `withVmPreserved`) on any caller block
`i < 619`. -/
theorem fromUtf8_placed_ok [LibsignalPlacement] {callerProg : Program} {i : Nat}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : LibsignalHooks} [IsLsBlockProg callerProg i ext]
    (hh : RunHooksPlaced A lim ext) (hookStack : Nat)
    (hi : i < 619 := by decide)
    (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg (lsρ lsFromUtf8Sym)
      (withLsCodeRoLoaded lsmpl (withVmPreserved (fromUtf8AsciiSpec hookStack))) :=
  subroutine_ok_withLsCodeRoLoaded_of_plain
    (ls_hook_ok_ultra_of_mem (prog := callerProg) (i := i)
      (hh.utf8 hookStack) (by decide) hi hunmut)

/-- `signal_session::address` (Block `580`) on any caller block `i < 619`. -/
theorem runAddress_placed_ok [LibsignalPlacement] {callerProg : Program} {i : Nat}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : LibsignalHooks} [IsLsBlockProg callerProg i ext]
    (hh : RunHooksPlaced A lim ext) (resStack : Nat)
    (hres : 0xB0 + extHookStack ≤ resStack) (hres64 : resStack ≤ 2 ^ 63)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 580)
      (withLsCodeRoLoaded lsmpl (addressSpec A lim uuidTryParse resStack)) := by
  have hmemrchr : subroutine_ok (lsProg_580 ext) (lsρ lsMemrchrSym)
      (withLsRoCl lsmpl (withVmPreserved (memrchrSpec extHookStack))) := by
    have hplain : subroutine_ok (lsProg_580 ext) (lsρ lsMemrchrSym)
        (withVmPreserved (memrchrSpec extHookStack)) := by
      dsimp only [lsProg_580]
      exact ls_hook_ok_ultra_of_mem (hh.memrchr extHookStack) (by decide)
    exact subroutine_ok_rocl_of_plain hplain
  have hrocl := address_placed_ok_rocl (prog := callerProg) (i := i)
    hh.allocFs hmemrchr hres hres64 hi
  refine subroutine_ok_mono hrocl (fun _ _ _ h => h) ?_ (fun _ _ _ _ hp => hp)
  intro x R s0 sf hpost
  dsimp only [withLsRoCl, withLsCodeRoLoaded] at hpost ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
  exact hpost.2

/-- `try_allocate_in [local#3]` (Block `588`) on any caller block `i < 619`. -/
theorem runTryAllocateIn3_placed_ok [LibsignalPlacement] {callerProg : Program} {i : Nat}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : LibsignalHooks} [IsLsBlockProg callerProg i ext]
    (hh : RunHooksPlaced A lim ext) (resStack : Nat)
    (hres : finishGrowStackX ≤ resStack) (hres64 : resStack ≤ 2 ^ 63)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 588)
      (withLsCodeRoLoaded lsmpl (tryAllocateInRustSpecOf resStack A lim).keepsFs) := by
  have hshim := AllocContractsFsPlaced.shim2_rocl (prog := lsProg_588 ext) (i := 588) hh.allocFs
  have halloc := allocNoOomExtern_fs_rocl (prog := lsProg_588 ext) (i := 588) hh.allocFs
  have hrocl := tryAllocateIn3_placed_okFs_of_hooks_at (prog := callerProg) (i := i)
    hshim halloc hres hres64 hi
  refine subroutine_ok_mono hrocl (fun _ _ _ h => h) ?_ (fun _ _ _ _ hp => hp)
  intro x R s0 sf hpost
  dsimp only [withLsRoCl, withLsCodeRoLoaded] at hpost ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
  exact hpost.2

/-- `do_reserve_and_handle [local#11]` (Block `561`) on any caller block `i < 619`. -/
theorem reserve_placed_ok [LibsignalPlacement] {callerProg : Program} {i : Nat}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : LibsignalHooks} [IsLsBlockProg callerProg i ext]
    (hh : RunHooksPlaced A lim ext) {resStack : Nat} (hstk : doReserveStackX ≤ resStack)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 561)
      (withLsCodeRoLoaded lsmpl (doReserveSpecOf resStack A lim)) := by
  have hrocl := cliDoReserve_placed_ok_at (prog := callerProg) (i := i)
    hh.alloc hstk
    (hh.panics "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error" (by decide)) hi
  refine subroutine_ok_mono hrocl (fun _ _ _ h => h) ?_ (fun _ _ _ _ hp => hp)
  intro x R s0 sf hpost
  dsimp only [withLsRoCl, withLsCodeRoLoaded] at hpost ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
  exact hpost.2

/-- `drop_glue<Stores>` (Block `550`) on any caller block `i < 619`. -/
theorem dropStores_placed_ok [LibsignalPlacement] {callerProg : Program} {i : Nat}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : LibsignalHooks} [IsLsBlockProg callerProg i ext]
    (hh : RunHooksPlaced A lim ext) (stk : Nat)
    (hstk : 96 + extHookStack ≤ stk) (hstk64 : stk ≤ 2 ^ 64)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (blkPl_550).base
      (dropStoresSpecPlaced M A lim stk) :=
  cliDropStores_placed_at_block hh.alloc stk hstk hstk64 hi

/-- `drop_glue<SignalMessage>` (Block `553`) on any caller block `i < 619`. -/
theorem dropSignalMessage_placed_ok [LibsignalPlacement] {callerProg : Program} {i : Nat}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : LibsignalHooks} [IsLsBlockProg callerProg i ext]
    (hh : RunHooksPlaced A lim ext) (stk : Nat)
    (hstk : 32 + extHookStack ≤ stk) (hstk64 : stk ≤ 2 ^ 64)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (blkPl_554).base
      (dropSignalMessageSpecPlaced M A lim stk) :=
  cliDropSignalMessage_placed_at_block hh.alloc stk hstk hstk64 hi

/-- `drop_glue<PreKeySignalMessage>` (Block `554`) on any caller block `i < 619`. -/
theorem dropPreKeyMsg_placed_ok [LibsignalPlacement] {callerProg : Program} {i : Nat}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : LibsignalHooks} [IsLsBlockProg callerProg i ext]
    (hh : RunHooksPlaced A lim ext) (stk : Nat)
    (hstk : 32 + extHookStack ≤ stk) (hstk64 : stk ≤ 2 ^ 64)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (blkPl_555).base
      (dropPreKeyMsgSpecPlaced M A lim stk) :=
  cliDropPreKeyMsg_placed_at_block hh.alloc stk hstk hstk64 hi

/-- `drop_glue<SignalProtocolError>` owned SPE contract (Block `552`) on any caller block
`i < 619`. -/
theorem dropSpeOwned_placed_ok [LibsignalPlacement] {callerProg : Program} {i : Nat}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : LibsignalHooks} [IsLsBlockProg callerProg i ext]
    (hh : RunHooksPlaced A lim ext)
    (hi : i < 619 := by decide) :
    DropSpeOwnedOkAtBlock callerProg A lim :=
  cliDropSpeOwned_placed_at_block hh.alloc hi

/-- `drop_glue<SignalProtocolError>` arbitrary-stack `.proto` contract (Block `552`) on any caller
block `i < 619`. -/
theorem dropSpe_placed_ok [LibsignalPlacement] {callerProg : Program} {i : Nat}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : LibsignalHooks} [IsLsBlockProg callerProg i ext]
    (hh : RunHooksPlaced A lim ext) (stk : Nat)
    (hstk : 32 + extHookStack ≤ stk) (hstk64 : stk ≤ 2 ^ 64)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (blkPl_553).base
      (dropSpeSpecStkPlaced A lim stk) :=
  cliDropSpe_placed_at_block hh.alloc stk hstk hstk64 hi

/-- `drop_glue<SignalProtocolError>` fixed-stack (`dropSpeStackX`) `.proto` contract (Block `552`)
on any caller block `i < 619`. -/
theorem dropSpeX_placed_ok [LibsignalPlacement] {callerProg : Program} {i : Nat}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : LibsignalHooks} [IsLsBlockProg callerProg i ext]
    (hh : RunHooksPlaced A lim ext)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (blkPl_553).base
      (withLsCodeRoLoaded lsmpl (dropSpeSpecX M A lim)) := by
  have hbase := cliDropSpe_placed_at_block (callerProg := callerProg) (i := i)
    hh.alloc dropSpeStackX (by decide) (by decide) hi
  refine subroutine_ok_mono hbase (fun _ _ _ hp => hp) ?_ (fun _ _ _ _ hp => hp)
  rintro ⟨x, st⟩ R s0 sf hpost
  refine Satisfies.mono (sepConj_mono_left ?_) hpost
  dsimp only [dropSpeSpecStkPlaced, withLsCodeRoLoaded,
    LibsignalBinary.Proofs.SignalSession.Cli.Pub.DropSpe.ProofBudget.dropSpeSpecStk, dropSpeSpecX]
  refine Entails.sepExists_elim fun evs => ?_
  refine Entails.pure_left fun ⟨htr, hevs⟩ => ?_
  have hex : A.pool lim (M.stepEvents evs st) sf ⊢
      ∃∗ evs' : List AllocEvent, ⌜FreeOnlyEvs evs'⌝ ∗ A.pool lim (M.stepEvents evs' st) sf :=
    Entails.sepExists_right evs (Entails.pure_right hevs (Entails.refl _))
  refine Entails.pure_right htr ?_
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left hex)) ?_
  exact Entails.of_eq (by sep_ac_rfl)

/-- `SignalMessage::try_from` (Block `85`) on any caller block `i < 619`. -/
theorem sigTryFrom_placed_ok [LibsignalPlacement] {callerProg : Program} {i : Nat}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {SigTryFromEnv : TryFromGhost → List AllocEvent → Prop} {ext : LibsignalHooks}
    [IsLsBlockProg callerProg i ext]
    (hSub : SubsetA4SigTryFromPlaced M A lim SigTryFromEnv ext)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (blkPl_85).base
      (tryFromSpecPlaced M A lim SigTryFromEnv) :=
  cliSigTryFrom_placed_at_block hSub hi

/-- `concat [local#3]` on two slices (Block `598`) on any caller block `i < 619`. -/
theorem concat_placed_ok [LibsignalPlacement] {callerProg : Program} {i : Nat}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : LibsignalHooks} [IsLsBlockProg callerProg i ext]
    (hh : RunHooksPlaced A lim ext) (stk : Nat)
    (hstk : 96 + extHookStack ≤ stk) (hstk64 : stk ≤ 2 ^ 64)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (blkPl_598).base
      (cliConcat2SpecPlaced M A lim stk) :=
  cliConcat2_placed_at_block hh.alloc hh.memcpyRO stk hstk hstk64 hi

/-- `signal_session::stores::path` (Block `596`) on any caller block `i < 619`. -/
theorem path_placed_ok [LibsignalPlacement] {callerProg : Program} {i : Nat}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : LibsignalHooks} [IsLsBlockProg callerProg i ext]
    (hh : RunHooksPlaced A lim ext) {stk : Nat}
    (hstk : pathNeed ≤ stk)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (blkPl_596).base
      (pathSpecPlaced A lim PathEnv stk) :=
  path_placed_caller_ok_of_deps (resProg := lsProg_596 ext) (resBlk := 596)
    hh.alloc hh.memcpyRO
    (reserve_placed_ok (callerProg := lsProg_596 ext) (i := 596) hh (Nat.le_refl _) (by decide))
    hstk hi (by decide) (by decide)

/-- `IdentityKey::decode` (Block `18`) over `A : RustCliAllocBudget M` on any caller block
`i < 619`. -/
theorem identityKeyDecode_placed_ok [LibsignalPlacement] {callerProg : Program} {i : Nat}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {ext : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i ext]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (blkPl_18).base
      (withLsCodeRoLoaded lsmpl (identityKeyDecodeRawSpec A)) := by
  have h18 : subroutine_ok ((blkPC_18).rebase (blkPl_18).base ext) (blkPl_18).base
      (withLsCodeRoLoaded lsmpl (identityKeyDecodeRawSpec A)) :=
    subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
      (identityKey_decode_placed_ok (A := A.repAlloc) ext)
  have hrocl := @ls_subroutine_ok_rocl_of_block _ _ callerProg
    ((blkPC_18).rebase (blkPl_18).base ext) i 18 ext
    hcaller (instIsLsBlockProg_18 ext) (blkPl_18).base _
    h18 _ _ _ _ hi (by decide) (by decide)
  refine subroutine_ok_mono hrocl (fun _ _ _ h => h) ?_ (fun _ _ _ _ hp => hp)
  intro x R s0 sf hpost
  dsimp only [withLsRoCl] at hpost
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
  exact hpost.2

/-- `PublicKey::deserialize` (Block `201`, ok and all error cases, `withVmPreserved`) on any caller
block `i < 619`. -/
theorem pkDeserializeFull_vm_placed_ok [LibsignalPlacement] {callerProg : Program} {i : Nat}
    (ext : LibsignalHooks)
    [hcaller : IsLsBlockProg callerProg i ext]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (blkPl_201).base
      (withLsCodeRoLoaded lsmpl (withVmPreserved deserializeFullPlacedSpec)) := by
  have h201 : subroutine_ok ((CryptoVerification.blkPC_201).rebase (blkPl_201).base ext)
      (blkPl_201).base (withLsCodeRoLoaded lsmpl (withVmPreserved deserializeFullPlacedSpec)) :=
    subroutine_ok_withLsCodeRoLoaded_of_plain (deserializeFull_vm_placed_ok ext)
  have hrocl := @ls_subroutine_ok_rocl_of_block _ _ callerProg
    ((CryptoVerification.blkPC_201).rebase (blkPl_201).base ext) i 201 ext
    hcaller (instIsLsBlockProg_201 ext) (blkPl_201).base _
    h201 _ _ _ _ hi (by decide) (by decide)
  refine subroutine_ok_mono hrocl (fun _ _ _ h => h) ?_ (fun _ _ _ _ hp => hp)
  intro x R s0 sf hpost
  dsimp only [withLsRoCl] at hpost
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
  exact hpost.2

/-- Constructs `RunHooksPlaced A lim (cliGhostExterns g baseExt)` from
`BaseHelperRows mmpl W baseExt` and `FsTHooks baseExt`. -/
theorem RunHooksPlaced.of_ghost [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (W : CliHooks) (baseExt : LibsignalHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (g : CliGhostHooks)
    (hBase : BaseHelperRows mmpl W baseExt)
    (hFsBase : FsTHooks baseExt)
    (hG : CliGhostSpqrAllocHooks M A lim g)
    (hStrFsT : ∀ f, g.stringClone = some f → HookFsTraced IsFsC f)
    (hStrClone : HookSat (cliGhostExterns g baseExt) lsStringCloneSym
      (stringCloneBudgetSpec M A lim))
    (hFmt : HookSat (cliGhostExterns g baseExt) lsFormatInnerSym
      (formatInnerBudgetSpec M A lim)) :
    RunHooksPlaced A lim (cliGhostExterns g baseExt) where
  alloc := allocContractsXCliPlaced_of_ghost mmpl W baseExt g hBase hG.toCliGhostAllocHooks
  allocFs := allocContractsFsPlaced_of_ghost mmpl W baseExt g hBase hG.toCliGhostAllocHooks
  panics := cliGhostExterns_panics g hBase.panics
  memcpyRO := cliGhostExterns_memcpyRegionRO_budget_sat baseExt hG.toCliGhostAllocHooks
  bcmp := hookSat_of_eq
    ((cliGhostExterns_other g baseExt (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans hBase.bcmp_eq)
    (cliExternsPlaced_bcmp_budget_sat mmpl W)
  fs prog i _ := traceFsSound_lsProg_ghost hG hStrFsT hFsBase prog i
  utf8 stk := hookSat_of_eq
    ((cliGhostExterns_other g baseExt (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans hBase.utf8_eq)
    (cliExternsPlaced_fromUtf8_budget_sat mmpl W stk)
  memrchr stk := hookSat_of_eq
    ((cliGhostExterns_other g baseExt (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans hBase.memrchr_eq)
    (cliExternsPlaced_memrchr_budget_sat mmpl W stk)
  codecHooks := codecHooksPlaced_of_ghost mmpl W baseExt g hBase hG.toCliGhostAllocHooks
  allocZeroed := ⟨g.allocZeroed, cliGhostExterns_allocZeroed g baseExt, hG.allocZeroed⟩
  stringClone := hStrClone
  formatInner := hFmt

/-- Constructs `RunHooksPlaced A lim (cliGhostExterns g (cliExternsPlaced mmpl W))` from
`CliGhostSpqrAllocHooks` and `HookSat` witnesses for `String::clone` and `format_inner`. -/
theorem RunHooksPlaced.of_hooks [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hG : CliGhostSpqrAllocHooks M A lim g)
    (hStrFsT : ∀ f, g.stringClone = some f → HookFsTraced IsFsC f)
    (hStrClone : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsStringCloneSym
      (stringCloneBudgetSpec M A lim))
    (hFmtInner : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsFormatInnerSym
      (formatInnerBudgetSpec M A lim)) :
    RunHooksPlaced A lim (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
  RunHooksPlaced.of_ghost mmpl W (cliExternsPlaced mmpl W) g
    (cliExternsPlaced_baseHelperRows mmpl W) (fsTHooks_cliExternsPlaced mmpl W)
    hG hStrFsT hStrClone hFmtInner

end LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget
