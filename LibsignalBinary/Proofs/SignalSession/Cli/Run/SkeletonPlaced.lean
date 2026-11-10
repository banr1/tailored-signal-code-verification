/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Skeleton
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.RunCodeSym
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.ReadFileHookPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Glue.BcmpHookPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Glue.FsTracedPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Concat2Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropPreKeyMsgPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropSignalMessagePlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropSpeOwnedPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropStoresPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.SigTryFromPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFromPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.StrlenUtf8A1Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AddressA1Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.TryAllocateIn3Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Reserve11Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.Placed
public import LibsignalBinary.Proofs.RecordCodecs.IdentityKeyDecode
public import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Deserialize
public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromHooks
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable Callee Slots and Hook Bundles for `signal_session::run`

Defines `CalleeSlot.OkPlaced`, `RunHooksPlaced`, and `RunCalleesPlaced` for Block `579`
(`signal_session::run`) under `[LibsignalPlacement]`, and transfers leaf and drop callee contracts
onto any caller block `i < 619`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false

namespace CryptoVerification.SignalSession.Cli.RunSkeleton

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open Arm64.Process
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.Run.Placed
open CryptoVerification.SignalSession.Cli.Slots
open CryptoVerification.SignalSession.Cli.RunGlue
open CryptoVerification.RecordCodecs.Placed

/-! ## Placed wrapper slots -/

/-- The slot's contract holds on `callerProg` at `target` for every budget `σ.need ≤ stk ≤ 2^63`. -/
def CalleeSlot.OkPlaced (callerProg : Program) (target : BitVec 64) (σ : CalleeSlot) : Prop :=
  ∀ stk, σ.need ≤ stk → stk ≤ 2 ^ 63 →
    subroutine_ok callerProg target (σ.spec stk)

/-! ## Placed hook and callee bundles -/

/-- Relocatable `[LibsignalPlacement]` extern hook hypotheses for `signal_session::run` (Block `579`). -/
structure RunHooksPlaced [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop where
  alloc : AllocContractsXCliPlaced A ext
  allocFs : AllocContractsFsPlaced A ext
  panics : Store.PlacedCommon.CliPanicHooksPlaced ext
  memcpyRO : HookSat ext lsMemcpySym SpqrV1.Alloc.sessionMemcpyRegionROSpec
  bcmp : HookSat ext "bcmp" cliBcmpSpec
  fs : ∀ (prog : Program) (i : Nat), [IsLsBlockProg prog i ext] → TraceFsSound prog
  utf8 : ∃ err, ext lsFromUtf8Sym = some (fromUtf8Hook err)
  memrchr : ext lsMemrchrSym = some memrchrHook
  codecHooks : RecordCodecsBinary.CodecHooksPlaced A ext
  allocZeroed : HookSat ext lsRustAllocZeroedSymCli (rustAllocZeroedSpec A)
  stringClone : HookSat ext lsStringCloneSym (LibsignalPublicApi.stringCloneSpec A)
  formatInner : HookSat ext lsFormatInnerSym (LibsignalTripleRatchet.formatInnerSpec A)

/-- Relocatable `[LibsignalPlacement]` callee contracts for `signal_session::run` (Block `579`, `lsProg_579 ext`). -/
structure RunCalleesPlaced [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) (B : RunBudgets) (σ : RunSlots) : Prop where
  /-- `read_file` at the stub (`lsReadFileSym`). -/
  readFile : subroutine_ok (lsProg_579 ext) (lsρ lsReadFileSym)
    (readFileSpecPlaced cliIo.rd cliWrOk A B.readFile)
  /-- `Dir::get` (`<signal_session::stores::Dir>::get`, Block `589`). -/
  dirGet : ∀ {stk : Nat}, B.dirGetNeed ≤ stk →
    subroutine_ok (lsProg_579 ext) (lsmpl.base 589)
      (dirGetSpecPlaced cliIo.rd cliWrOk A stk)
  /-- `read_bundle::{closure#0}` (Block `563`). -/
  bundleRead : ∀ {stk : Nat}, B.bundleReadNeed ≤ stk →
    subroutine_ok (lsProg_579 ext) (lsmpl.base 563)
      (bundleReadSpecPlaced cliIo.rd cliWrOk A stk)
  /-- `split_id` (Block `593`). -/
  splitId : ∀ {stk : Nat}, splitIdNeed ≤ stk →
    subroutine_ok (lsProg_579 ext) (lsmpl.base 593)
      (splitIdSpecPlaced A stk)
  /-- `split_signed` (Block `592`). -/
  splitSigned : ∀ {stk : Nat}, splitSignedNeed ≤ stk →
    subroutine_ok (lsProg_579 ext) (lsmpl.base 592)
      (splitSignedSpecPlaced A stk)
  /-- `drop_glue<SPE> [local#4]` fixed-stack contract (Block `552`). -/
  dropSpeX : subroutine_ok (lsProg_579 ext) (blkPl_553).base
    (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (dropSpeSpecX A))
  /-- `drop_glue<SPE> [local#4]` arbitrary-stack contract (Block `552`). -/
  dropSpe : ∀ (stk : Nat), 32 + extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    subroutine_ok (lsProg_579 ext) (blkPl_553).base
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (dropSpeSpecStk A stk))
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

/-- `core::str::converts::from_utf8` (`lsFromUtf8Sym`) on any caller block `i < 619`. -/
theorem fromUtf8_placed_ok [LibsignalPlacement] {callerProg : Program} {i : Nat}
    {A : RustAlloc} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg i ext]
    (hh : RunHooksPlaced A ext) (hookStack : Nat)
    (hi : i < 619 := by decide)
    (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg (lsρ lsFromUtf8Sym)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (fromUtf8AsciiSpec hookStack)) := by
  obtain ⟨err, hext⟩ := hh.utf8
  exact LibsignalPublicApi.StoreKit.subroutine_ok_withLsCodeRoLoaded_of_plain
    (ls_hook_ok_ultra_of_mem (prog := callerProg) (i := i)
      ⟨fromUtf8Hook err, hext, fromUtf8Hook_ok hookStack err⟩ (by decide) hi hunmut)

/-- `signal_session::address` (Block `580`) on any caller block `i < 619`. -/
theorem runAddress_placed_ok [LibsignalPlacement] {callerProg : Program} {i : Nat}
    {A : RustAlloc} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg i ext]
    (hh : RunHooksPlaced A ext) (resStack : Nat)
    (hres : 0xB0 + extHookStack ≤ resStack) (hres64 : resStack ≤ 2 ^ 63)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 580)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (addressSpec A uuidTryParse resStack)) := by
  have hmemrchr : subroutine_ok (lsProg_580 ext) (lsρ lsMemrchrSym)
      (withLsRoCl lsmpl (memrchrSpec extHookStack)) := by
    have hsat : HookSat ext lsMemrchrSym (memrchrSpec extHookStack) :=
      ⟨memrchrHook, hh.memrchr, memrchrHook_ok extHookStack⟩
    have hplain : subroutine_ok (lsProg_580 ext) (lsρ lsMemrchrSym) (memrchrSpec extHookStack) := by
      dsimp only [lsProg_580]
      exact ls_hook_ok_ultra_of_mem hsat (by decide)
    apply subroutine_ok_outcome_intro
    intro x R s0 hpc hrun hpre hsp hL
    dsimp only [withLsRoCl] at hpre
    rw [sepConj_comm ((memrchrSpec extHookStack).pre x s0), sepConj_assoc,
      satisfies_pure_sepConj] at hpre
    rcases hpre with ⟨hcrl0, hpre⟩
    obtain ⟨sf, hsteps, hout⟩ := hplain.to_outcome x R s0 hpc hrun hpre hsp hL
    refine ⟨sf, hsteps, ?_⟩
    rcases hout with ⟨hret, hcc, hpost⟩ | hrest
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [withLsRoCl]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨Address.Helpers.lscro_of_keepsFrozen hcrl0 hsteps.keepsFrozen, hpost⟩
    · exact Or.inr hrest
  have hrocl := address_placed_ok_rocl (prog := callerProg) (i := i)
    hh.allocFs
    (hh.panics "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error" (by decide))
    hmemrchr hres hres64 hi
  refine subroutine_ok_mono hrocl (fun _ _ _ h => h) ?_ (fun _ _ _ _ hp => hp)
  intro x R s0 sf hpost
  dsimp only [withLsRoCl, LibsignalPublicApi.StoreKit.withLsCodeRoLoaded] at hpost ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
  exact hpost.2

/-- `try_allocate_in [local#3]` (Block `588`) on any caller block `i < 619`. -/
theorem runTryAllocateIn3_placed_ok [LibsignalPlacement] {callerProg : Program} {i : Nat}
    {A : RustAlloc} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg i ext]
    (hh : RunHooksPlaced A ext) (resStack : Nat)
    (hres : finishGrowStackX ≤ resStack) (hres64 : resStack ≤ 2 ^ 63)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 588)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (tryAllocateInSpecOf resStack A).keepsFs) := by
  have hrocl := tryAllocateIn3_placed_okFs_at (prog := callerProg) (i := i)
    hh.allocFs hres hres64 hi
  refine subroutine_ok_mono hrocl (fun _ _ _ h => h) ?_ (fun _ _ _ _ hp => hp)
  intro x R s0 sf hpost
  dsimp only [withLsRoCl, LibsignalPublicApi.StoreKit.withLsCodeRoLoaded] at hpost ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
  exact hpost.2

/-- `do_reserve_and_handle [local#11]` (Block `561`) on any caller block `i < 619`. -/
theorem reserve_placed_ok [LibsignalPlacement] {callerProg : Program} {i : Nat}
    {A : RustAlloc} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg i ext]
    (hh : RunHooksPlaced A ext) {resStack : Nat} (hstk : doReserveStackX ≤ resStack)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 561)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (SpqrV1.Varint.doReserveSpecOf resStack A)) := by
  have hrocl := cliDoReserve_placed_ok_at (prog := callerProg) (i := i)
    hh.alloc hstk
    (hh.panics "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error" (by decide)) hi
  refine subroutine_ok_mono hrocl (fun _ _ _ h => h) ?_ (fun _ _ _ _ hp => hp)
  intro x R s0 sf hpost
  dsimp only [withLsRoCl, LibsignalPublicApi.StoreKit.withLsCodeRoLoaded] at hpost ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
  exact hpost.2

/-- `drop_glue<Stores>` (Block `550`) on any caller block `i < 619`. -/
theorem dropStores_placed_ok [LibsignalPlacement] {callerProg : Program} {i : Nat}
    {A : RustAlloc} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg i ext]
    (hh : RunHooksPlaced A ext) (stk : Nat)
    (hstk : 96 + extHookStack ≤ stk) (hstk64 : stk ≤ 2 ^ 64)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (blkPl_550).base
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (dropStoresSpec A stk)) :=
  RunProofs.cliDropStores_placed_at_block hh.alloc stk hstk hstk64 hi

/-- `drop_glue<SignalMessage>` (Block `553`) on any caller block `i < 619`. -/
theorem dropSignalMessage_placed_ok [LibsignalPlacement] {callerProg : Program} {i : Nat}
    {A : RustAlloc} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg i ext]
    (hh : RunHooksPlaced A ext) (stk : Nat)
    (hstk : 32 + extHookStack ≤ stk) (hstk64 : stk ≤ 2 ^ 64)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (blkPl_554).base
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (dropSignalMessageSpec A stk)) :=
  RunProofs.cliDropSignalMessage_placed_at_block hh.alloc stk hstk hstk64 hi

/-- `drop_glue<PreKeySignalMessage>` (Block `554`) on any caller block `i < 619`. -/
theorem dropPreKeyMsg_placed_ok [LibsignalPlacement] {callerProg : Program} {i : Nat}
    {A : RustAlloc} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg i ext]
    (hh : RunHooksPlaced A ext) (stk : Nat)
    (hstk : 32 + extHookStack ≤ stk) (hstk64 : stk ≤ 2 ^ 64)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (blkPl_555).base
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (dropPreKeyMsgSpec A stk)) :=
  RunProofs.cliDropPreKeyMsg_placed_at_block hh.alloc stk hstk hstk64 hi

/-- `drop_glue<SignalProtocolError>` owned SPE contract (Block `552`) on any caller block `i < 619`. -/
theorem dropSpeOwned_placed_ok [LibsignalPlacement] {callerProg : Program} {i : Nat}
    {A : RustAlloc} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg i ext]
    (hh : RunHooksPlaced A ext)
    (hi : i < 619 := by decide) :
    RunDrop.DropSpeOwnedOkAtBlock callerProg A :=
  RunProofs.cliDropSpeOwned_placed_at_block hh.alloc hi

/-- `SignalMessage::try_from` (Block `85`) on any caller block `i < 619`. -/
theorem sigTryFrom_placed_ok [LibsignalPlacement] {callerProg : Program} {i : Nat}
    {A : RustAlloc} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg i ext]
    (hSub : RunProofs.SubsetA4SigTryFromPlaced A ext)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (blkPl_85).base
      (RunProofs.tryFromSpecPlaced A) :=
  RunProofs.cliSigTryFrom_placed_at_block hSub hi

/-- `concat [local#3]` on two slices (Block `598`) on any caller block `i < 619`. -/
theorem concat_placed_ok [LibsignalPlacement] {callerProg : Program} {i : Nat}
    {A : RustAlloc} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg i ext]
    (hh : RunHooksPlaced A ext) (stk : Nat)
    (hstk : 96 + extHookStack ≤ stk) (hstk64 : stk ≤ 2 ^ 64)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (blkPl_598).base
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (cliConcat2Spec A stk)) :=
  RunProofs.cliConcat2_placed_at_block hh.alloc hh.memcpyRO
    (hh.panics "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error" (by decide))
    stk hstk hstk64 hi

/-- `signal_session::stores::path` (Block `596`) on any caller block `i < 619`. -/
theorem path_placed_ok [LibsignalPlacement] {callerProg : Program} {i : Nat}
    {A : RustAlloc} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg i ext]
    (hh : RunHooksPlaced A ext) {stk : Nat}
    (hstk : pathNeed ≤ stk)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (blkPl_596).base
      (pathSpecPlaced A stk) :=
  Path.Helpers.path_placed_caller_ok_of_deps (resProg := lsProg_596 ext) (resBlk := 596)
    hh.alloc hh.panics hh.memcpyRO
    (reserve_placed_ok (callerProg := lsProg_596 ext) (i := 596) hh (Nat.le_refl _) (by decide))
    hstk hi (by decide) (by decide)

/-- `IdentityKey::decode` (Block `18`) on any caller block `i < 619`. -/
theorem identityKeyDecode_placed_ok [LibsignalPlacement] {callerProg : Program} {i : Nat}
    {A : RustAlloc} {ext : String → Option (State → State)}
    [hcaller : IsLsBlockProg callerProg i ext]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (blkPl_18).base
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (RecordCodecsBinary.identityKeyDecodeRawSpec A)) := by
  have h18 : subroutine_ok ((blkPC_18).rebase (blkPl_18).base ext) (blkPl_18).base
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (RecordCodecsBinary.identityKeyDecodeRawSpec A)) :=
    LibsignalPublicApi.StoreKit.subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
      (RecordCodecsBinary.IdentityKeyDecode.identityKey_decode_placed_ok ext)
  have hrocl := @ls_subroutine_ok_rocl_of_block _ _ callerProg
    ((blkPC_18).rebase (blkPl_18).base ext) i 18 ext
    hcaller (instIsLsBlockProg_18 ext) (blkPl_18).base _
    h18 _ _ _ _ hi (by decide) (by decide)
  refine subroutine_ok_mono hrocl (fun _ _ _ h => h) ?_ (fun _ _ _ _ hp => hp)
  intro x R s0 sf hpost
  dsimp only [withLsRoCl] at hpost
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
  exact hpost.2

/-- `PublicKey::deserialize` (Block `201`, ok case only) on any caller block `i < 619`. -/
theorem pkDeserialize_placed_ok [LibsignalPlacement] {callerProg : Program} {i : Nat}
    (ext : String → Option (State → State))
    [hcaller : IsLsBlockProg callerProg i ext]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (blkPl_201).base
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        LibsignalSession.FindReceiverChainIndex.deserializePlacedSpec) := by
  have h201 : subroutine_ok ((blkPC_201).rebase (blkPl_201).base ext) (blkPl_201).base
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        LibsignalSession.FindReceiverChainIndex.deserializePlacedSpec) :=
    LibsignalPublicApi.StoreKit.subroutine_ok_withLsCodeRoLoaded_of_plain
      (LibsignalSession.FindReceiverChainIndex.deserialize_placed_ok ext)
  have hrocl := @ls_subroutine_ok_rocl_of_block _ _ callerProg
    ((blkPC_201).rebase (blkPl_201).base ext) i 201 ext
    hcaller (CryptoVerification.instIsLsBlockProg_201 ext) (blkPl_201).base _
    h201 _ _ _ _ hi (by decide) (by decide)
  refine subroutine_ok_mono hrocl (fun _ _ _ h => h) ?_ (fun _ _ _ _ hp => hp)
  intro x R s0 sf hpost
  dsimp only [withLsRoCl] at hpost
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
  exact hpost.2

/-- `PublicKey::deserialize` (Block `201`, ok and all error cases) on any caller block `i < 619`. -/
theorem pkDeserializeFull_placed_ok [LibsignalPlacement] {callerProg : Program} {i : Nat}
    (ext : String → Option (State → State))
    [hcaller : IsLsBlockProg callerProg i ext]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (blkPl_201).base
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        LibsignalTripleRatchet.Wire.deserializeFullPlacedSpec) := by
  have h201 : subroutine_ok ((blkPC_201).rebase (blkPl_201).base ext) (blkPl_201).base
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        LibsignalTripleRatchet.Wire.deserializeFullPlacedSpec) :=
    LibsignalPublicApi.StoreKit.subroutine_ok_withLsCodeRoLoaded_of_plain
      (LibsignalTripleRatchet.Wire.deserializeFull_placed_ok ext)
  have hrocl := @ls_subroutine_ok_rocl_of_block _ _ callerProg
    ((blkPC_201).rebase (blkPl_201).base ext) i 201 ext
    hcaller (CryptoVerification.instIsLsBlockProg_201 ext) (blkPl_201).base _
    h201 _ _ _ _ hi (by decide) (by decide)
  refine subroutine_ok_mono hrocl (fun _ _ _ h => h) ?_ (fun _ _ _ _ hp => hp)
  intro x R s0 sf hpost
  dsimp only [withLsRoCl] at hpost
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
  exact hpost.2

/-- Instantiates `RunHooksPlaced` at `cliGhostExterns g (cliExternsPlaced mmpl W)` and `E2E.HooksE.A0`. -/
theorem RunHooksPlaced.cli [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostA0Hooks E2E.HooksE.A0 g)
    (hStrFsT : ∀ f, g.stringClone = some f → HookFsTraced IsFsC f)
    (hStrClone : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsStringCloneSym
      (LibsignalPublicApi.stringCloneSpec E2E.HooksE.A0))
    (hFmtInner : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsFormatInnerSym
      (LibsignalTripleRatchet.formatInnerSpec E2E.HooksE.A0)) :
    RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns g (cliExternsPlaced mmpl W)) where
  alloc := allocContractsXCliPlaced_cli mmpl g W hG
  allocFs := allocContractsFsPlaced_cli mmpl g W hG
  panics := fun _ hmem => cliGhostExterns_panic_of_mem mmpl g W hmem
  memcpyRO := cliExternsPlaced_memcpyRegionRO_sat mmpl g W hG
  bcmp := cliGhostExterns_sat_of_cliExternsPlaced mmpl g W (cli_hookSat_bcmp_placed mmpl W)
  fs := fun _ _ => traceFsSound_lsProg_cli_ghost mmpl g W (cliGhostA0Hooks_to_fs hG hStrFsT)
  utf8 := ⟨W.utf8Err, cliGhostExterns_fromUtf8_eq mmpl g W⟩
  memrchr := cliGhostExterns_memrchr_eq mmpl g W
  codecHooks := codecHooksPlaced_cli mmpl g W hG
  allocZeroed := cliExternsPlaced_allocZeroed_sat mmpl g W hG
  stringClone := hStrClone
  formatInner := hFmtInner

end CryptoVerification.SignalSession.Cli.RunSkeleton
