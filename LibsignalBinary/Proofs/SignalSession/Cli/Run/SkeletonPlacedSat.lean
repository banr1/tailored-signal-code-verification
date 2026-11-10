/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlaced -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AddressA1PlacedSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.StrlenUtf8A1PlacedSat -- proof-setup: allow-public-import
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# `HookSat` Sibling of `SkeletonPlaced` (`SkeletonPlacedSat`)

Provides `RunHooksPlacedSat` — the `HookSat`-parameterized sibling of
`RunHooksPlaced` (`SkeletonPlaced.lean:85`) replacing both
- `utf8 : ∃ err, ext lsFromUtf8Sym = some (fromUtf8Hook err)` with
  `utf8 : HookSat ext lsFromUtf8Sym (fromUtf8AsciiSpec extHookStack)`, and
- `memrchr : ext lsMemrchrSym = some memrchrHook` with
  `memrchr : HookSat ext lsMemrchrSym (memrchrSpec extHookStack)` —
together with `RunHooksPlaced.toSat`, `fromUtf8_placed_ok_sat`, `fromUtf8_placed_ok_ext_sat`,
`runAddress_placed_ok_sat`, and the companion `RunHooksPlacedSat` projections.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedSat

open Arm64 ProofLib
open CryptoVerification
  (IsLsBlockProg LibsignalPlacement libsignalMutatedBlocks ls_hook_ok_ultra_of_mem lsmpl lsρ)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.LibsignalTripleRatchetRepr (uuidTryParse)
open CryptoVerification.LibsignalTripleRatchet
  (doReserveStackX extHookStack finishGrowStackX lsMemcpySym rustAllocZeroedSpec)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (TraceFsSound subroutine_ok_rocl_of_plain subroutine_ok_withLsCodeRoLoaded_of_plain
   subroutine_ok_withLsCodeRoLoaded_of_rocl withLsCodeRoLoaded withLsRoCl)
open CryptoVerification.SignalSession
  (lsFormatInnerSym lsFromUtf8Sym lsMemrchrSym lsRustAllocZeroedSymCli lsStringCloneSym)
open CryptoVerification.SignalSession.Cli (cliBcmpSpec pathSpecPlaced)
open CryptoVerification.SignalSession.Cli.RunProofs
  (cliConcat2Spec dropPreKeyMsgSpec dropSignalMessageSpec dropStoresSpec)
open CryptoVerification.SignalSession.Cli.MainHops
  (AllocContractsFsPlaced AllocContractsXCliPlaced addressSpec address_placed_ok_rocl_ls
   cliDoReserve_placed_ok_at fromUtf8AsciiSpec memrchrSpec tryAllocateIn3_placed_okFs_at
   tryAllocateInSpecOf)
open CryptoVerification.SignalSession.Cli.Placed
  (blkPl_550 blkPl_554 blkPl_555 blkPl_596 blkPl_598 lsProg_580 lsProg_596)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunHooksPlaced pathNeed)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet (withLsRet)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AddressA1PlacedSat
  (hookSat_memrchr_ls_of_eq)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.StrlenUtf8A1PlacedSat
  (hookSat_fromUtf8_of_eq)

/-- `HookSat` sibling of `RunHooksPlaced` (`SkeletonPlaced.lean:85`), replacing `utf8` and
    `memrchr` exact-hook equations with `HookSat` at `extHookStack`. -/
structure RunHooksPlacedSat [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop where
  alloc : AllocContractsXCliPlaced A ext
  allocFs : AllocContractsFsPlaced A ext
  panics : CryptoVerification.SignalSession.Cli.Store.PlacedCommon.CliPanicHooksPlaced ext
  memcpyRO : HookSat ext lsMemcpySym CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpec
  bcmp : HookSat ext "bcmp" cliBcmpSpec
  fs : ∀ (prog : Program) (i : Nat), [IsLsBlockProg prog i ext] → TraceFsSound prog
  utf8 : HookSat ext lsFromUtf8Sym (fromUtf8AsciiSpec extHookStack)
  memrchr : HookSat ext lsMemrchrSym (withLsRet (memrchrSpec extHookStack))
  codecHooks : CryptoVerification.RecordCodecsBinary.CodecHooksPlaced A ext
  allocZeroed : HookSat ext lsRustAllocZeroedSymCli (rustAllocZeroedSpec A)
  stringClone : HookSat ext lsStringCloneSym
    (CryptoVerification.LibsignalPublicApi.stringCloneSpec A)
  formatInner : HookSat ext lsFormatInnerSym
    (CryptoVerification.LibsignalTripleRatchet.formatInnerSpec A)

/-- Coercion `RunHooksPlaced → RunHooksPlacedSat` via `hookSat_fromUtf8_of_eq` and
    `hookSat_memrchr_ls_of_eq`. -/
theorem RunHooksPlaced.toSat [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)} (hh : RunHooksPlaced A ext) :
    RunHooksPlacedSat A ext where
  alloc := hh.alloc
  allocFs := hh.allocFs
  panics := hh.panics
  memcpyRO := hh.memcpyRO
  bcmp := hh.bcmp
  fs := hh.fs
  utf8 := let ⟨_, hext⟩ := hh.utf8; hookSat_fromUtf8_of_eq extHookStack hext
  memrchr := hookSat_memrchr_ls_of_eq hh.memrchr
  codecHooks := hh.codecHooks
  allocZeroed := hh.allocZeroed
  stringClone := hh.stringClone
  formatInner := hh.formatInner

/-- `HookSat` sibling of `fromUtf8_placed_ok` (`SkeletonPlaced.lean:144`) at arbitrary `hookStack`. -/
theorem fromUtf8_placed_ok_sat [LibsignalPlacement] {callerProg : Program} {i : Nat}
    {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg i ext]
    {hookStack : Nat}
    (hutf8 : HookSat ext lsFromUtf8Sym (fromUtf8AsciiSpec hookStack))
    (hi : i < 619 := by decide)
    (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg (lsρ lsFromUtf8Sym)
      (withLsCodeRoLoaded lsmpl (fromUtf8AsciiSpec hookStack)) :=
  subroutine_ok_withLsCodeRoLoaded_of_plain
    (ls_hook_ok_ultra_of_mem (prog := callerProg) (i := i) hutf8 (by decide) hi hunmut)

/-- `RunHooksPlacedSat` projection of `fromUtf8_placed_ok_sat` at `extHookStack` (matching every
    `R0ProofPlaced*` call site). -/
theorem fromUtf8_placed_ok_ext_sat [LibsignalPlacement] {callerProg : Program} {i : Nat}
    {A : RustAlloc} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg i ext]
    (hh : RunHooksPlacedSat A ext)
    (hi : i < 619 := by decide)
    (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg (lsρ lsFromUtf8Sym)
      (withLsCodeRoLoaded lsmpl (fromUtf8AsciiSpec extHookStack)) :=
  fromUtf8_placed_ok_sat (callerProg := callerProg) (i := i) hh.utf8 hi hunmut

/-- `HookSat` sibling of `runAddress_placed_ok` (`SkeletonPlaced.lean:158`). -/
theorem runAddress_placed_ok_sat [LibsignalPlacement] {callerProg : Program} {i : Nat}
    {A : RustAlloc} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg i ext]
    (hh : RunHooksPlacedSat A ext) (resStack : Nat)
    (hres : 0xB0 + extHookStack ≤ resStack) (hres64 : resStack ≤ 2 ^ 63)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 580)
      (withLsCodeRoLoaded lsmpl (addressSpec A uuidTryParse resStack)) := by
  have hmemrchr : subroutine_ok (lsProg_580 ext) (lsρ lsMemrchrSym)
      (withLsRoCl lsmpl (withLsRet (memrchrSpec extHookStack))) := by
    have hplain : subroutine_ok (lsProg_580 ext) (lsρ lsMemrchrSym)
        (withLsRet (memrchrSpec extHookStack)) := by
      dsimp only [lsProg_580]
      exact ls_hook_ok_ultra_of_mem hh.memrchr (by decide)
    exact subroutine_ok_rocl_of_plain hplain
  exact subroutine_ok_withLsCodeRoLoaded_of_rocl
    (address_placed_ok_rocl_ls (prog := callerProg) (i := i)
      hh.allocFs
      (hh.panics "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error" (by decide))
      hmemrchr hres hres64 hi)

/-- `HookSat` sibling of `runTryAllocateIn3_placed_ok` (`SkeletonPlaced.lean:198`). -/
theorem runTryAllocateIn3_placed_ok_sat [LibsignalPlacement] {callerProg : Program} {i : Nat}
    {A : RustAlloc} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg i ext]
    (hh : RunHooksPlacedSat A ext) (resStack : Nat)
    (hres : finishGrowStackX ≤ resStack) (hres64 : resStack ≤ 2 ^ 63)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 588)
      (withLsCodeRoLoaded lsmpl (tryAllocateInSpecOf resStack A).keepsFs) :=
  subroutine_ok_withLsCodeRoLoaded_of_rocl
    (tryAllocateIn3_placed_okFs_at (prog := callerProg) (i := i)
      hh.allocFs hres hres64 hi)

/-- `HookSat` sibling of `reserve_placed_ok` (`SkeletonPlaced.lean:215`). -/
theorem reserve_placed_ok_sat [LibsignalPlacement] {callerProg : Program} {i : Nat}
    {A : RustAlloc} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg i ext]
    (hh : RunHooksPlacedSat A ext) {resStack : Nat} (hstk : doReserveStackX ≤ resStack)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 561)
      (withLsCodeRoLoaded lsmpl
        (CryptoVerification.SpqrV1.Varint.doReserveSpecOf resStack A)) :=
  subroutine_ok_withLsCodeRoLoaded_of_rocl
    (cliDoReserve_placed_ok_at (prog := callerProg) (i := i)
      hh.alloc hstk
      (hh.panics "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error" (by decide)) hi)

/-- `HookSat` sibling of `dropStores_placed_ok` (`SkeletonPlaced.lean:233`). -/
theorem dropStores_placed_ok_sat [LibsignalPlacement] {callerProg : Program} {i : Nat}
    {A : RustAlloc} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg i ext]
    (hh : RunHooksPlacedSat A ext) (stk : Nat)
    (hstk : 96 + extHookStack ≤ stk) (hstk64 : stk ≤ 2 ^ 64)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (blkPl_550).base
      (withLsCodeRoLoaded lsmpl (dropStoresSpec A stk)) :=
  CryptoVerification.SignalSession.Cli.RunProofs.cliDropStores_placed_at_block
    hh.alloc stk hstk hstk64 hi

/-- `HookSat` sibling of `dropSignalMessage_placed_ok` (`SkeletonPlaced.lean:244`). -/
theorem dropSignalMessage_placed_ok_sat [LibsignalPlacement] {callerProg : Program} {i : Nat}
    {A : RustAlloc} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg i ext]
    (hh : RunHooksPlacedSat A ext) (stk : Nat)
    (hstk : 32 + extHookStack ≤ stk) (hstk64 : stk ≤ 2 ^ 64)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (blkPl_554).base
      (withLsCodeRoLoaded lsmpl (dropSignalMessageSpec A stk)) :=
  CryptoVerification.SignalSession.Cli.RunProofs.cliDropSignalMessage_placed_at_block
    hh.alloc stk hstk hstk64 hi

/-- `HookSat` sibling of `dropPreKeyMsg_placed_ok` (`SkeletonPlaced.lean:255`). -/
theorem dropPreKeyMsg_placed_ok_sat [LibsignalPlacement] {callerProg : Program} {i : Nat}
    {A : RustAlloc} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg i ext]
    (hh : RunHooksPlacedSat A ext) (stk : Nat)
    (hstk : 32 + extHookStack ≤ stk) (hstk64 : stk ≤ 2 ^ 64)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (blkPl_555).base
      (withLsCodeRoLoaded lsmpl (dropPreKeyMsgSpec A stk)) :=
  CryptoVerification.SignalSession.Cli.RunProofs.cliDropPreKeyMsg_placed_at_block
    hh.alloc stk hstk hstk64 hi

/-- `HookSat` sibling of `dropSpeOwned_placed_ok` (`SkeletonPlaced.lean:266`). -/
theorem dropSpeOwned_placed_ok_sat [LibsignalPlacement] {callerProg : Program} {i : Nat}
    {A : RustAlloc} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg i ext]
    (hh : RunHooksPlacedSat A ext)
    (hi : i < 619 := by decide) :
    CryptoVerification.SignalSession.Cli.RunDrop.DropSpeOwnedOkAtBlock callerProg A :=
  CryptoVerification.SignalSession.Cli.RunProofs.cliDropSpeOwned_placed_at_block hh.alloc hi

/-- `HookSat` sibling of `concat_placed_ok` (`SkeletonPlaced.lean:285`). -/
theorem concat_placed_ok_sat [LibsignalPlacement] {callerProg : Program} {i : Nat}
    {A : RustAlloc} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg i ext]
    (hh : RunHooksPlacedSat A ext) (stk : Nat)
    (hstk : 96 + extHookStack ≤ stk) (hstk64 : stk ≤ 2 ^ 64)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (blkPl_598).base
      (withLsCodeRoLoaded lsmpl (cliConcat2Spec A stk)) :=
  CryptoVerification.SignalSession.Cli.RunProofs.cliConcat2_placed_at_block hh.alloc hh.memcpyRO
    (hh.panics "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error" (by decide))
    stk hstk hstk64 hi

/-- `HookSat` sibling of `path_placed_ok` (`SkeletonPlaced.lean:298`). -/
theorem path_placed_ok_sat [LibsignalPlacement] {callerProg : Program} {i : Nat}
    {A : RustAlloc} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg i ext]
    (hh : RunHooksPlacedSat A ext) {stk : Nat}
    (hstk : pathNeed ≤ stk)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (blkPl_596).base
      (pathSpecPlaced A stk) :=
  CryptoVerification.SignalSession.Cli.Path.Helpers.path_placed_caller_ok_of_deps
    (resProg := lsProg_596 ext) (resBlk := 596)
    hh.alloc hh.panics hh.memcpyRO
    (reserve_placed_ok_sat (callerProg := lsProg_596 ext) (i := 596) hh (Nat.le_refl _) (by decide))
    hstk hi (by decide) (by decide)

end LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedSat
