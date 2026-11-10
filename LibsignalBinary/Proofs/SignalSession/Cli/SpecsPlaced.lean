/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.StoreKit.Placed
public import LibsignalBinary.Proofs.SignalSession.Coins.CoinsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.StoreSpecs.Session
public import LibsignalBinary.Proofs.SignalSession.Cli.StoreSpecs.Identity
public import LibsignalBinary.Proofs.SignalSession.Cli.StoreSpecs.KpkMark
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.SpecDefs
public import LibsignalBinary.Proofs.SignalSession.Cli.CliTokenPatchPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Callees
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.MainCodeSym
public import LibsignalBinary.Proofs.SpqrV1.GF.Mul2U16
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.LogClosure
public import LibsignalBinary.Specifications.SignalSession.CliBinaryPq
public import LibsignalBinary.Specifications.SignalSession.CliProcess
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Process

/-!
# Relocatable CLI Hook Table, Function Specifications, and Process Composition

Defines `[LibsignalPlacement]` counterparts of the mangled-symbol CLI hook table and process
execution predicates (`cliHookTablePlaced`, `cliExternsPlaced`, `cliProgPlaced`, `CliRunsToPlaced`,
`cliRunPlacedSig`), relocatable function-level specs across `Dir`, `Public`, `StoreSpecs`,
`Initiate`, and `Main` (`pathSpecPlaced`, `decimalSpecPlaced`, `readFileSpecPlaced`, store shim/poll
specs, `mainSpecPlaced`, `outcome_of_main_placed`), and `MainHops` callee/I/O bundles
(`AllocContractsXCliPlaced`, `AllocContractsFsPlaced`, `MainCalleesPlaced`, `MainIoPlaced`,
`runSpecPlaced`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

/-! ## 1. Mangled-symbol CLI hook table and `ProcessRunsTo` -/

namespace CryptoVerification.SignalSession

open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoGames CryptoGames.LibsignalSession

/-- Block `617` (`main`) program under `[LibsignalPlacement]` with `cliExternsPlaced mmpl W`. -/
noncomputable def cliProgPlaced [LibsignalPlacement] (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    Program :=
  libsignalSessionLib.blockProgram lsmpl 617 (cliExternsPlaced mmpl W)

/-- Block `617` (`main`) program under `[LibsignalPlacement]` with `cliExternsPlacedSig mmpl W`. -/
noncomputable abbrev cliProgPlacedSig [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (W : CliHooks) : Program :=
  Placed.cliProgPlacedSig lsmpl mmpl W

abbrev CliRunsToPlaced [LibsignalPlacement] (mmpl : Obj.MultiPlacement) (elf : ElfImage)
    (W : CliHooks) (i : Inputs) (o : Outcome) : Prop :=
  Placed.CliRunsToPlaced lsmpl mmpl elf W i o

noncomputable abbrev cliRunPlacedSig [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (elf : ElfImage) (W : CliHooks) : CliRun :=
  Placed.cliRunPlacedSig lsmpl mmpl elf W

noncomputable def cliRunOfPlaced [LibsignalPlacement] (mmpl : Obj.MultiPlacement) (elf : ElfImage)
    (W : CliHooks) : CliRun :=
  fun i =>
    (outcomeOf elf (cliProgPlaced mmpl W)
      (processInputs ("libsignal-cli" :: i.argv) i.stdin i.files i.dirs)).map toOutcome

/-- Non-null placed `futDrop` address: `lsmpl.base 547` when non-zero (all well-formed ELFs load at
`≥ 4096`), falling back to `1#64` at `0#64`. -/
def lsDropOffPlaced [LibsignalPlacement] : BitVec 64 :=
  if lsmpl.base 547 == 0#64 then 1#64 else lsmpl.base 547

theorem lsDropOffPlaced_eq [LibsignalPlacement] (h : lsmpl.base 547 ≠ 0#64) :
    lsDropOffPlaced = lsmpl.base 547 := by
  unfold lsDropOffPlaced
  rw [beq_eq_false_iff_ne.mpr h]
  rfl

theorem lsDropOffPlaced_ne_zero [LibsignalPlacement] :
    0#64 + lsDropOffPlaced ≠ 0#64 := by
  rw [BitVec.zero_add]
  unfold lsDropOffPlaced
  split
  · decide
  · rename_i h
    intro h0
    exact h (beq_iff_eq.mpr h0)

end CryptoVerification.SignalSession

/-! ## 2. Relocatable function-level CLI specifications -/

namespace CryptoVerification.SignalSession.Cli

open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary

/-! ### `path` and `decimal` -/

def pathSpecPlaced [LibsignalPlacement] (A : RustAlloc) (stk : Nat) : Spec PathGhost :=
  LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.ret ∧ s.readReg64 .x1 = x.dirA ∧
          (s.readReg64 .x2).toNat = x.dir.length ∧ s.readReg64 .x3 = x.nameA ∧
          (s.readReg64 .x4).toNat = x.name.length ∧
          x.dir.length < 2 ^ 32 ∧ x.name.length < 2 ^ 32⌝ ∗
          SpqrV1.ChainProofs.bytesAt x.dirRo x.dirA x.dir ∗
          SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗ memRegion x.ret 24 ∗
          stackAt s.sp stk ∗ A.pool
      post := fun x s0 sf =>
        ⌜sf.trace = s0.trace⌝ ∗ vecU8 A x.ret (x.dir ++ [0x2f#8] ++ x.name) ∗
          SpqrV1.ChainProofs.bytesAt x.dirRo x.dirA x.dir ∗
          SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗ stackAt s0.sp stk ∗ A.pool
      onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }

def decimalSpecPlaced [LibsignalPlacement] (A : RustAlloc) (stk : Nat) : Spec DecimalGhost :=
  LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.ret ∧ s.readReg32 .x1 = x.n⌝ ∗ memRegion x.ret 24 ∗
          stackAt s.sp stk ∗ A.pool
      post := fun x s0 sf =>
        ⌜sf.trace = s0.trace⌝ ∗ vecU8 A x.ret (decimalText x.n.toNat) ∗
          stackAt s0.sp stk ∗ A.pool
      onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }

/-! ### Directory helpers (`read_file`, `address_text`, `grow_one`, `Dir::put`, `Dir::get`) -/

/-- Hook-level `read_file` specification (without `inImage` or `withLsCodeRoLoaded`, suitable for `HookSat`). -/
def readFileSpecPlaced (rd : ReadRule) (pathOk : List (BitVec 8) → Prop) (A : RustAlloc)
    (stk : Nat) : Spec ReadFileGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.pathA ∧ (s.readReg64 .x1).toNat = x.path.length ∧
      s.readReg64 .x8 = x.ret ∧ x.path.length < 2 ^ 32 ∧ pathOk x.path⌝ ∗
      (x.pathA ↦ₛ x.path) ∗ memRegion x.ret 24 ∗ stackAt s.sp stk ∗ A.pool
  post := fun x s0 sf =>
    (∃∗ r : Except Unit (List (BitVec 8)),
      ⌜r = rd s0.fs.files x.path ∧ sf.trace = s0.trace⌝ ∗ ioVecAt A x.ret r) ∗
      (x.pathA ↦ₛ x.path) ∗ stackAt s0.sp stk ∗ A.pool
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

def addrTextSpecPlaced [LibsignalPlacement] (A : RustAlloc) (stk : Nat) : Spec AddrTextGhost :=
  LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.ret ∧ s.readReg64 .x1 = x.addr ∧ x.g.name.bytes.length < 2 ^ 32⌝ ∗
          protocolAddressAt A x.g x.addr ∗ memRegion x.ret 24 ∗ stackAt s.sp stk ∗ A.pool
      post := fun x s0 sf =>
        ⌜sf.trace = s0.trace⌝ ∗ vecU8 A x.ret (addressText x.g.val) ∗
          protocolAddressAt A x.g x.addr ∗ stackAt s0.sp stk ∗ A.pool
      onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }

def growOneDirSpecPlaced [LibsignalPlacement] (A : RustAlloc) (stk : Nat) : Spec GrowOneDirGhost :=
  LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.v ∧ x.cap.toNat < 2 ^ 32⌝ ∗
          RustHeap.vecAt A 48 8 (dirEntryAt A) x.v x.cap x.ptr x.xs ∗ stackAt s.sp stk ∗ A.pool
      post := fun x s0 sf =>
        ⌜sf.trace = s0.trace⌝ ∗
          (∃∗ ptr' : BitVec 64, RustHeap.vecAt A 48 8 (dirEntryAt A) x.v
            (BitVec.ofNat 64 (max (2 * x.cap.toNat) 4)) ptr' x.xs) ∗
          stackAt s0.sp stk ∗ A.pool
      onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }

def dirPutSpecPlaced [LibsignalPlacement] (A : RustAlloc) (stk : Nat) : Spec DirPutGhost :=
  LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.self ∧ s.readReg64 .x1 = x.nameV ∧ s.readReg64 .x2 = x.bytesV ∧
          x.dir.changed.length < 2 ^ 32⌝ ∗
          dirAt A x.self x.dir ∗ vecU8 A x.nameV x.name ∗ vecU8 A x.bytesV x.bytes ∗
          stackAt s.sp stk ∗ A.pool
      post := fun x s0 sf =>
        ⌜sf.trace = s0.trace⌝ ∗ dirAt A x.self (x.dir.put x.name x.bytes) ∗
          memRegion x.nameV 24 ∗ memRegion x.bytesV 24 ∗ stackAt s0.sp stk ∗ A.pool
      onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }

def dirPutStrSpecPlaced [LibsignalPlacement] (A : RustAlloc) (stk : Nat) : Spec DirPutStrGhost :=
  LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.self ∧ s.readReg64 .x1 = x.nameA ∧
          (s.readReg64 .x2).toNat = x.name.length ∧ s.readReg64 .x3 = x.bytesV ∧
          x.name.length < 2 ^ 32 ∧ x.dir.changed.length < 2 ^ 32⌝ ∗
          dirAt A x.self x.dir ∗ SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
          vecU8 A x.bytesV x.bytes ∗ stackAt s.sp stk ∗ A.pool
      post := fun x s0 sf =>
        ⌜sf.trace = s0.trace⌝ ∗ dirAt A x.self (x.dir.put x.name x.bytes) ∗
          SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗ memRegion x.bytesV 24 ∗
          stackAt s0.sp stk ∗ A.pool
      onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }

def dirGetSpecPlaced [LibsignalPlacement] (rd : ReadRule) (pathOk : List (BitVec 8) → Prop)
    (A : RustAlloc) (stk : Nat) : Spec DirGetGhost :=
  LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.ret ∧ s.readReg64 .x1 = x.self ∧ s.readReg64 .x2 = x.nameA ∧
          (s.readReg64 .x3).toNat = x.name.length ∧ x.name.length < 2 ^ 32 ∧
          x.dir.path.length < 2 ^ 32 ∧ pathOk (pathOf x.dir.path x.name)⌝ ∗
          dirAt A x.self x.dir ∗ SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
          memRegion x.ret 48 ∗ stackAt s.sp stk ∗ A.pool
      post := fun x s0 sf =>
        (∃∗ r : Except Unit (List (BitVec 8)),
          ⌜r = x.dir.get rd s0.fs.files x.name ∧ sf.trace = s0.trace⌝ ∗
            getResultAt A x.ret r) ∗
          dirAt A x.self x.dir ∗ SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
          stackAt s0.sp stk ∗ A.pool
      onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }

/-! ### Bundle helpers (`split_id`, `split_signed`, `read_bundle::{closure#0}`) -/

def splitIdSpecPlaced [LibsignalPlacement] (A : RustAlloc) (stk : Nat) : Spec SplitGhost :=
  LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.ret ∧ s.readReg64 .x1 = x.fp ∧
          (s.readReg64 .x2).toNat = x.file.length⌝ ∗
          SpqrV1.ChainProofs.bytesAt x.ro x.fp x.file ∗ memRegion x.ret 48 ∗
          stackAt s.sp stk ∗ A.pool
      post := fun x s0 sf =>
        ⌜sf.trace = s0.trace⌝ ∗ splitIdResultAt A x.ret x.fp x.file ∗
          SpqrV1.ChainProofs.bytesAt x.ro x.fp x.file ∗ stackAt s0.sp stk ∗ A.pool
      onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }

def splitSignedSpecPlaced [LibsignalPlacement] (A : RustAlloc) (stk : Nat) : Spec SplitGhost :=
  LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.ret ∧ s.readReg64 .x1 = x.fp ∧
          (s.readReg64 .x2).toNat = x.file.length⌝ ∗
          SpqrV1.ChainProofs.bytesAt x.ro x.fp x.file ∗ memRegion x.ret 48 ∗
          stackAt s.sp stk ∗ A.pool
      post := fun x s0 sf =>
        ⌜sf.trace = s0.trace⌝ ∗ splitSignedResultAt A x.ret x.fp x.file ∗
          SpqrV1.ChainProofs.bytesAt x.ro x.fp x.file ∗ stackAt s0.sp stk ∗ A.pool
      onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }

def bundleReadSpecPlaced [LibsignalPlacement] (rd : ReadRule) (pathOk : List (BitVec 8) → Prop)
    (A : RustAlloc) (stk : Nat) : Spec BundleReadGhost :=
  LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.ret ∧ s.readReg64 .x1 = x.dirA ∧
          (s.readReg64 .x2).toNat = x.dir.length ∧ s.readReg64 .x3 = x.nameA ∧
          (s.readReg64 .x4).toNat = x.name.length ∧ x.dir.length < 2 ^ 32 ∧
          x.name.length < 2 ^ 32 ∧ pathOk (x.dir ++ [0x2f#8] ++ x.name)⌝ ∗
          SpqrV1.ChainProofs.bytesAt x.dirRo x.dirA x.dir ∗
          SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗ memRegion x.ret 48 ∗
          stackAt s.sp stk ∗ A.pool
      post := fun x s0 sf =>
        (∃∗ r : Except Unit (List (BitVec 8)),
          ⌜r = rd s0.fs.files (x.dir ++ [0x2f#8] ++ x.name) ∧ sf.trace = s0.trace⌝ ∗
            getResultAt A x.ret r) ∗
          SpqrV1.ChainProofs.bytesAt x.dirRo x.dirA x.dir ∗
          SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗ stackAt s0.sp stk ∗ A.pool
      onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }

/-! ### Future vtable `.rodata` symbols and store specifications -/

abbrev sessLoadFutVtSym : String := "libsignal_cli:.rodata..Lanon.85"
abbrev sessStoreFutVtSym : String := "libsignal_cli:.rodata..Lanon.86"
abbrev idSaveFutVtSym : String := "libsignal_cli:.rodata..Lanon.81"
abbrev idTrustFutVtSym : String := "libsignal_cli:.rodata..Lanon.82"
abbrev idKeyPairFutVtSym : String := "libsignal_cli:.rodata..Lanon.83"
abbrev idRegIdFutVtSym : String := "libsignal_cli:.rodata..Lanon.84"
abbrev spkGetFutVtSym : String := "libsignal_cli:.rodata..Lanon.87"
abbrev pkGetFutVtSym : String := "libsignal_cli:.rodata..Lanon.89"
abbrev pkRemoveFutVtSym : String := "libsignal_cli:.rodata..Lanon.91"
abbrev kpkGetFutVtSym : String := "libsignal_cli:.rodata..Lanon.92"
abbrev kpkMarkFutVtSym : String := "libsignal_cli:.rodata..Lanon.94"

/-- Trait vtable `.rodata` symbols of `Stores::open()` / `run`. -/
abbrev cliSessionVtSym : String := "libsignal_cli:.rodata..Lanon.34"
abbrev cliIdentityVtSym : String := "libsignal_cli:.rodata..Lanon.35"
abbrev cliPreKeyVtSym : String := "libsignal_cli:.rodata..Lanon.36"
abbrev cliSignedPreKeyVtSym : String := "libsignal_cli:.rodata..Lanon.37"
abbrev cliKyberPreKeyVtSym : String := "libsignal_cli:.rodata..Lanon.38"

def sessLoadShimSpecPlaced [LibsignalPlacement] (A : RustAlloc) (stk : Nat) : Spec LoadShimCall :=
  LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.self ∧ s.readReg64 .x1 = x.addrA⌝ ∗ A.pool ∗ stackAt s.sp stk
      post := fun x s0 sf =>
        ⌜sf.readReg64 .x1 = lsρ sessLoadFutVtSym ∧ sf.readReg64 .x0 ≠ 0#64 ∧
          (sf.readReg64 .x0).toNat % 8 = 0 ∧ sf.trace = s0.trace⌝ ∗
          A.live (sf.readReg64 .x0) 24 8 ∗ sessLoadBoxAt (sf.readReg64 .x0) x.self x.addrA 0#8 ∗
          A.pool ∗ stackAt s0.sp stk
      onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }

def sessStoreShimSpecPlaced [LibsignalPlacement] (A : RustAlloc) (stk : Nat) : Spec StoreShimCall :=
  LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.self ∧ s.readReg64 .x1 = x.addrA ∧ s.readReg64 .x2 = x.recA⌝ ∗
          A.pool ∗ stackAt s.sp stk
      post := fun x s0 sf =>
        ⌜sf.readReg64 .x1 = lsρ sessStoreFutVtSym ∧ sf.readReg64 .x0 ≠ 0#64 ∧
          (sf.readReg64 .x0).toNat % 8 = 0 ∧ sf.trace = s0.trace⌝ ∗
          A.live (sf.readReg64 .x0) 32 8 ∗
          sessStoreBoxAt (sf.readReg64 .x0) x.self x.addrA x.recA 0#8 ∗
          A.pool ∗ stackAt s0.sp stk
      onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }

noncomputable def sessDeserializeSpecPlaced [LibsignalPlacement]
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (A : RustAlloc) :
    Spec E2E.Record.DeserializeGeneral.DeserializeGenGhost :=
  LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.p ∧
          s.readReg64 .x1 = BitVec.ofNat 64 (E2E.Record.encodeRecord x.r).length ∧
          s.readReg64 .x8 = x.out ∧ Scope x.r⌝ ∗
          (x.p ↦ₛ E2E.Record.encodeRecord x.r) ∗ memRegion x.out 368 ∗
          stackAt s.sp E2E.Record.recDeserializeStack
      post := fun x s0 sf =>
        ⌜sf.trace = s0.trace⌝ ∗ (x.p ↦ₛ E2E.Record.encodeRecord x.r) ∗
          (∃∗ g : E2E.Record.RecordGhost, ⌜E2E.Record.Serialization.CanonRecord g x.r⌝ ∗
            E2E.Record.sessionRecordAt A x.out g x.r) ∗
          stackAt s0.sp E2E.Record.recDeserializeStack
      onPanic := E2E.Record.Serialization.allocPanic }

def sessLoadPollSpecPlaced [LibsignalPlacement] (rd : ReadRule) (pathOk : List (BitVec 8) → Prop)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (A : RustAlloc)
    (stk : Nat) : Spec SessLoadPollGhost :=
  LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.call.fut ∧ s.readReg64 .x8 = x.call.out ∧
          x.call.addr.name.bytes.length < 2 ^ 32 ∧
          (addressText x.call.addr.val).length < 2 ^ 32 ∧ x.dir.path.length < 2 ^ 32 ∧
          pathOk (pathOf x.dir.path (addressText x.call.addr.val)) ∧
          ∀ bs, x.dir.get rd s.fs.files (addressText x.call.addr.val) = .ok bs →
            SessFileWf Scope bs⌝ ∗
          sessLoadBoxAt x.call.fut x.self x.call.addrA 0#8 ∗ dirAt A x.self x.dir ∗
          memRegion x.call.out 368 ∗ protocolAddressAt A x.call.addr x.call.addrA ∗
          A.pool ∗ stackAt s.sp stk
      post := fun x s0 sf =>
        (∃∗ gr : Except Unit (List (BitVec 8)),
          ∃∗ ans : Except Unit (Option (SessionRecord (List (BitVec 8)))),
          ⌜(gr = x.dir.get rd s0.fs.files (addressText x.call.addr.val) ∧ sf.trace = s0.trace) ∧
            SessLoadAns Scope gr ans⌝ ∗
          sessLoadOutAt A x.call.out ans) ∗
          sessLoadBoxAt x.call.fut x.self x.call.addrA 1#8 ∗ dirAt A x.self x.dir ∗
          protocolAddressAt A x.call.addr x.call.addrA ∗ A.pool ∗ stackAt s0.sp stk
      onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }

def sessStorePollSpecPlaced [LibsignalPlacement] (A : RustAlloc) (stk : Nat) :
    Spec SessStorePollGhost :=
  LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.call.fut ∧ s.readReg64 .x8 = x.call.out ∧
          x.call.call.addr.name.bytes.length < 2 ^ 32 ∧
          (E2E.Record.encodeRecord x.call.call.record).length < 2 ^ 32 ∧
          x.dir.changed.length < 2 ^ 32⌝ ∗
          sessStoreBoxAt x.call.fut x.self x.call.call.addrA x.call.call.recA 0#8 ∗
          dirAt A x.self x.dir ∗ memRegion x.call.out 48 ∗
          protocolAddressAt A x.call.call.addr x.call.call.addrA ∗
          sessionRecordAt A x.call.call.recA x.call.call.g x.call.call.record ∗
          A.pool ∗ stackAt s.sp stk
      post := fun x s0 sf =>
        ⌜sf.trace = s0.trace⌝ ∗
          sessStoreBoxAt x.call.fut x.self x.call.call.addrA x.call.call.recA 1#8 ∗
          dirAt A x.self (x.dir.put (addressText x.call.call.addr.val)
            (E2E.Record.encodeRecord x.call.call.record)) ∗
          (x.call.out ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗ memRegion (x.call.out + 8#64) 40 ∗
          protocolAddressAt A x.call.call.addr x.call.call.addrA ∗
          sessionRecordAt A x.call.call.recA x.call.call.g x.call.call.record ∗
          A.pool ∗ stackAt s0.sp stk
      onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }

def idSaveShimSpecPlaced [LibsignalPlacement] (A : RustAlloc) (stk : Nat) :
    Spec IdentityShimCall :=
  LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.self ∧ s.readReg64 .x1 = x.addrA ∧ s.readReg64 .x2 = x.keyA⌝ ∗
          A.pool ∗ stackAt s.sp stk
      post := fun x s0 sf =>
        ⌜sf.readReg64 .x1 = lsρ idSaveFutVtSym ∧ sf.readReg64 .x0 ≠ 0#64 ∧
          (sf.readReg64 .x0).toNat % 8 = 0 ∧ sf.trace = s0.trace⌝ ∗
          A.live (sf.readReg64 .x0) 32 8 ∗
          idSaveBoxAt (sf.readReg64 .x0) x.self x.addrA x.keyA 0#8 ∗
          A.pool ∗ stackAt s0.sp stk
      onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }

def idTrustShimSpecPlaced [LibsignalPlacement] (A : RustAlloc) (stk : Nat) :
    Spec (IdentityShimCall × BitVec 8) :=
  LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
    { pre := fun (x, d) s =>
        ⌜s.readReg64 .x0 = x.self ∧ s.readReg64 .x1 = x.addrA ∧ s.readReg64 .x2 = x.keyA ∧
          (s.readReg64 .x3).setWidth 8 = d⌝ ∗ A.pool ∗ stackAt s.sp stk
      post := fun (x, d) s0 sf =>
        ⌜sf.readReg64 .x1 = lsρ idTrustFutVtSym ∧ sf.readReg64 .x0 ≠ 0#64 ∧
          (sf.readReg64 .x0).toNat % 8 = 0 ∧ sf.trace = s0.trace⌝ ∗
          A.live (sf.readReg64 .x0) 32 8 ∗
          idTrustBoxAt (sf.readReg64 .x0) x.self x.addrA x.keyA 0#8 d ∗
          A.pool ∗ stackAt s0.sp stk
      onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }

def idTrustPollSpecPlaced [LibsignalPlacement] (rd : ReadRule) (pathOk : List (BitVec 8) → Prop)
    (A : RustAlloc) (stk : Nat) : Spec (IdPollGhost × BitVec 8) :=
  LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
    { pre := fun (x, d) s =>
        ⌜s.readReg64 .x0 = x.call.fut ∧ s.readReg64 .x8 = x.call.out ∧
          x.call.call.addr.name.bytes.length < 2 ^ 32 ∧ x.peers.path.length < 2 ^ 32 ∧
          pathOk (pathOf x.peers.path x.call.call.addr.val.name) ∧
          ∀ bs, x.peers.get rd s.fs.files x.call.call.addr.val.name = .ok bs → IdFileWf bs⌝ ∗
          idTrustBoxAt x.call.fut x.self x.call.call.addrA x.call.call.keyA 0#8 d ∗
          dirAt A (x.self + 0x28#64) x.peers ∗ memRegion x.call.out 48 ∗
          protocolAddressAt A x.call.call.addr x.call.call.addrA ∗
          (x.call.call.keyA ↦ₛ x.call.call.key.publicKey.bytes.toList) ∗
          FromRecordCallees.lsLogOff ∗ A.pool ∗ stackAt s.sp stk
      post := fun (x, d) s0 sf =>
        (∃∗ gr : Except Unit (List (BitVec 8)),
          ∃∗ p : Except Unit (Option IdentityKey),
          ⌜(gr = x.peers.get rd s0.fs.files x.call.call.addr.val.name ∧ sf.trace = s0.trace) ∧
            IdPeerAns gr p⌝ ∗
          idTrustOutAt A x.call.out (idTrustOf p x.call.call.key)) ∗
          idTrustBoxAt x.call.fut x.self x.call.call.addrA x.call.call.keyA 1#8 d ∗
          dirAt A (x.self + 0x28#64) x.peers ∗
          protocolAddressAt A x.call.call.addr x.call.call.addrA ∗
          (x.call.call.keyA ↦ₛ x.call.call.key.publicKey.bytes.toList) ∗
          FromRecordCallees.lsLogOff ∗ A.pool ∗ stackAt s0.sp stk
      onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }

def idSavePollSpecPlaced [LibsignalPlacement] (rd : ReadRule) (pathOk : List (BitVec 8) → Prop)
    (A : RustAlloc) (stk : Nat) : Spec IdPollGhost :=
  LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.call.fut ∧ s.readReg64 .x8 = x.call.out ∧
          x.call.call.addr.name.bytes.length < 2 ^ 32 ∧ x.peers.path.length < 2 ^ 32 ∧
          x.peers.changed.length < 2 ^ 32 ∧
          pathOk (pathOf x.peers.path x.call.call.addr.val.name) ∧
          ∀ bs, x.peers.get rd s.fs.files x.call.call.addr.val.name = .ok bs → IdFileWf bs⌝ ∗
          idSaveBoxAt x.call.fut x.self x.call.call.addrA x.call.call.keyA 0#8 ∗
          dirAt A (x.self + 0x28#64) x.peers ∗ memRegion x.call.out 48 ∗
          protocolAddressAt A x.call.call.addr x.call.call.addrA ∗
          (x.call.call.keyA ↦ₛ x.call.call.key.publicKey.bytes.toList) ∗
          FromRecordCallees.lsLogOff ∗ A.pool ∗ stackAt s.sp stk
      post := fun x s0 sf =>
        (∃∗ gr : Except Unit (List (BitVec 8)),
          ∃∗ p : Except Unit (Option IdentityKey),
          ⌜(gr = x.peers.get rd s0.fs.files x.call.call.addr.val.name ∧ sf.trace = s0.trace) ∧
            IdPeerAns gr p⌝ ∗
          idSaveOutAt A x.call.out (idSaveOf p x.call.call.key) ∗
          dirAt A (x.self + 0x28#64)
            (idSavePeers x.peers x.call.call.addr.val.name x.call.call.key p)) ∗
          idSaveBoxAt x.call.fut x.self x.call.call.addrA x.call.call.keyA 1#8 ∗
          protocolAddressAt A x.call.call.addr x.call.call.addrA ∗
          (x.call.call.keyA ↦ₛ x.call.call.key.publicKey.bytes.toList) ∗
          FromRecordCallees.lsLogOff ∗ A.pool ∗ stackAt s0.sp stk
      onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }

def pkShimSpecPlaced [LibsignalPlacement] (vtSym : String) (A : RustAlloc) (stk : Nat) :
    Spec PkShimCall :=
  LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.self ∧ s.readReg32 .x1 = x.id⌝ ∗ A.pool ∗ stackAt s.sp stk
      post := fun x s0 sf =>
        ⌜sf.readReg64 .x1 = lsρ vtSym ∧ sf.readReg64 .x0 ≠ 0#64 ∧
          (sf.readReg64 .x0).toNat % 8 = 0 ∧ sf.trace = s0.trace⌝ ∗
          A.live (sf.readReg64 .x0) 16 8 ∗ pkBoxAt (sf.readReg64 .x0) x.self x.id 0#8 ∗
          A.pool ∗ stackAt s0.sp stk
      onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }

def kpkMarkShimSpecPlaced [LibsignalPlacement] (A : RustAlloc) (stk : Nat) :
    Spec KpkMarkShimCall :=
  LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.self ∧ s.readReg32 .x1 = x.id ∧ s.readReg32 .x2 = x.signedId ∧
          s.readReg64 .x3 = x.baseKeyA⌝ ∗ A.pool ∗ stackAt s.sp stk
      post := fun x s0 sf =>
        ⌜sf.readReg64 .x1 = lsρ kpkMarkFutVtSym ∧ sf.readReg64 .x0 ≠ 0#64 ∧
          (sf.readReg64 .x0).toNat % 8 = 0 ∧ sf.trace = s0.trace⌝ ∗
          A.live (sf.readReg64 .x0) 32 8 ∗
          kpkMarkBoxAt (sf.readReg64 .x0) x.self x.baseKeyA x.id x.signedId 0#8 ∗
          A.pool ∗ stackAt s0.sp stk
      onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }

def pkGetPollSpecOfPlaced [LibsignalPlacement] {α : Type}
    (dec : List (BitVec 8) → Except SignalProtocolError α)
    (resAt : RustAlloc → BitVec 64 → Except SignalProtocolError α → SepProp) (size w : Nat)
    (rd : ReadRule) (pathOk : List (BitVec 8) → Prop) (A : RustAlloc)
    (stk : Nat) : Spec PkPollGhost :=
  LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.fut ∧ s.readReg64 .x8 = x.out ∧ PkNameOk pathOk x.dir x.id ∧
          PkSizeOk rd s.fs.files x.dir x.id⌝ ∗
          pkBoxAt x.fut x.self x.id 0#8 ∗ dirAt A x.self x.dir ∗ memRegion x.out size ∗
          A.pool ∗ stackAt s.sp stk
      post := fun x s0 sf =>
        (∃∗ ans : PkAns α,
          ⌜ans = pkAnsOf dec (x.dir.get rd s0.fs.files (keyName x.id)) ∧ sf.trace = s0.trace⌝ ∗
          pkAnsAt A resAt size w x.out ans) ∗
          pkBoxAt x.fut x.self x.id 1#8 ∗ dirAt A x.self x.dir ∗ A.pool ∗ stackAt s0.sp stk
      onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }

abbrev spkGetPollSpecPlaced [LibsignalPlacement] (rd : ReadRule) (pathOk : List (BitVec 8) → Prop)
    (A : RustAlloc) (stk : Nat) : Spec PkPollGhost :=
  pkGetPollSpecOfPlaced SignedPreKeyRecord.deserialize signedPreKeyResultAt 88 14 rd pathOk A stk

abbrev pkGetPollSpecPlaced [LibsignalPlacement] (rd : ReadRule) (pathOk : List (BitVec 8) → Prop)
    (A : RustAlloc) (stk : Nat) : Spec PkPollGhost :=
  pkGetPollSpecOfPlaced PreKeyRecord.deserialize preKeyResultAt 56 13 rd pathOk A stk

def pkRemovePollSpecPlaced [LibsignalPlacement] (rd : ReadRule) (pathOk : List (BitVec 8) → Prop)
    (A : RustAlloc) (stk : Nat) : Spec PkPollGhost :=
  LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.fut ∧ s.readReg64 .x8 = x.out ∧ PkNameOk pathOk x.dir x.id ∧
          x.dir.changed.length < 2 ^ 32⌝ ∗
          pkBoxAt x.fut x.self x.id 0#8 ∗ dirAt A x.self x.dir ∗ memRegion x.out 48 ∗
          A.pool ∗ stackAt s.sp stk
      post := fun x s0 sf =>
        (∃∗ res : Except Unit Unit × DirGhost,
          ⌜res = pkRemoveOf x.dir (keyName x.id) (x.dir.get rd s0.fs.files (keyName x.id)) ∧
              sf.trace = s0.trace⌝ ∗
          pkRemoveOutAt A x.out res.1 ∗ dirAt A x.self res.2) ∗
          pkBoxAt x.fut x.self x.id 1#8 ∗ A.pool ∗ stackAt s0.sp stk
      onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }

def kpkGetPollSpecPlaced [LibsignalPlacement] (rd : ReadRule) (pathOk : List (BitVec 8) → Prop)
    (A : RustAlloc) (stk : Nat) : Spec KpkPollGhost :=
  LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.fut ∧ s.readReg64 .x8 = x.out ∧
          PkNameOk pathOk x.kg.oneTime x.id ∧ PkNameOk pathOk x.kg.lastResort x.id ∧
          PkSizeOk rd s.fs.files x.kg.oneTime x.id ∧ PkSizeOk rd s.fs.files x.kg.lastResort x.id⌝ ∗
          pkBoxAt x.fut x.self x.id 0#8 ∗ dirAt A x.self x.kg.oneTime ∗
          dirAt A (x.self + 0x28#64) x.kg.lastResort ∗ memRegion x.out 88 ∗
          A.pool ∗ stackAt s.sp stk
      post := fun x s0 sf =>
        (∃∗ ans : PkAns KyberPreKeyRecord,
          ⌜ans = kpkAnsOf
                (pkAnsOf KyberPreKeyRecord.deserialize
                  (x.kg.oneTime.get rd s0.fs.files (keyName x.id)))
                (pkAnsOf KyberPreKeyRecord.deserialize
                  (x.kg.lastResort.get rd s0.fs.files (keyName x.id))) ∧
              sf.trace = s0.trace⌝ ∗
          kpkAnsAt A x.out ans) ∗
          pkBoxAt x.fut x.self x.id 1#8 ∗ dirAt A x.self x.kg.oneTime ∗
          dirAt A (x.self + 0x28#64) x.kg.lastResort ∗ A.pool ∗ stackAt s0.sp stk
      onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }

def dropSpeWordSpecPlaced [LibsignalPlacement] (A : RustAlloc) : Spec DropSpeWordGhost :=
  LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.a ∧ (x.w = 13 ∨ x.w = 14)⌝ ∗
          (x.a ↦₆₄ speWord x.w) ∗ memRegion (x.a + 8#64) 40 ∗ A.pool ∗
          stackAt s.sp Getters.dropSpeStackX
      post := fun x s0 sf =>
        ⌜sf.trace = s0.trace⌝ ∗ memRegion x.a 48 ∗ A.pool ∗ stackAt s0.sp Getters.dropSpeStackX }

def kpkMarkPollSpecPlaced [LibsignalPlacement] (rd : ReadRule) (pathOk : List (BitVec 8) → Prop)
    (A : RustAlloc) (stk : Nat) : Spec KpkMarkPollGhost :=
  LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.fut ∧ s.readReg64 .x8 = x.out ∧
          PkNameOk pathOk x.kg.oneTime x.id ∧ KpkBaseKeysOk pathOk x.kg.lastResort x.id ∧
          KpkSeenOk rd s.fs.files x.kg.lastResort x.id x.signedId x.baseKey ∧
          x.kg.oneTime.changed.length < 2 ^ 32 ∧ x.kg.lastResort.changed.length < 2 ^ 32⌝ ∗
          kpkMarkBoxAt x.fut x.self x.baseKeyA x.id x.signedId 0#8 ∗
          dirAt A x.self x.kg.oneTime ∗ dirAt A (x.self + 0x28#64) x.kg.lastResort ∗
          (x.baseKeyA ↦ₛ x.baseKey.bytes.toList) ∗ memRegion x.out 48 ∗
          A.pool ∗ stackAt s.sp stk
      post := fun x s0 sf =>
        (∃∗ res : KpkMarkAns × KyberGhost,
          ⌜res = kpkMarkOf rd s0.fs.files x.kg x.id x.signedId x.baseKey ∧
              sf.trace = s0.trace⌝ ∗
          kpkMarkOutAt A x.out res.1 ∗
          dirAt A x.self res.2.oneTime ∗ dirAt A (x.self + 0x28#64) res.2.lastResort) ∗
          kpkMarkBoxAt x.fut x.self x.baseKeyA x.id x.signedId 1#8 ∗
          (x.baseKeyA ↦ₛ x.baseKey.bytes.toList) ∗ A.pool ∗ stackAt s0.sp stk
      onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }

/-! ### `main` statics, entry precondition, and process composition -/

def coinsStaticsPlaced [LibsignalPlacement] : SepProp :=
  (∃∗ v : BitVec 64, Coins.coinsNextPlaced ↦₆₄ v) ∗
    (∃∗ v : BitVec 64, Coins.coinsLeftPlaced ↦₆₄ v)

def cliStaticsPlaced [LibsignalPlacement] : SepProp :=
  coinsStaticsPlaced ∗ SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ FromRecordCallees.lsLogOff

/-- Entry memory predicate of `main` parameterized by `CodeOk : Memory → Prop`. -/
def mainEntryPrePlaced (CodeOk : Memory → Prop) (A : RustAlloc) (stk : Nat) (Statics : SepProp)
    (i : Inputs) (s : State) : SepProp :=
  ⌜CodeOk s.mem ∧ stk ≤ s.sp.toNat⌝ ∗ mainFrame A stk Statics i s

def mainSpecPlaced (CodeOk : Memory → Prop) (A : RustAlloc) (stk : Nat) (Statics : SepProp)
    (Run : Inputs → RunAnswer → Prop) : Spec MainGhost where
  pre := fun g s =>
    ⌜CodeOk s.mem ∧ MainCaseB2 Run IsSendOverCap IsStdinOverCap g.i g.r ∧ CliInputsOk g.i ∧
      MainEntryFacts g.i s ∧ stk ≤ s.sp.toNat⌝ ∗
      mainFrame A stk Statics g.i s
  post := fun g s0 sf => ⌜MainPost g.r s0 sf ∨ allocFailedIn s0 sf⌝ ∗ stackAt s0.sp stk ∗ anyHeap
  onPanic := fun g s0 sf => ⌜g.r = .abort ∨ allocFailedIn s0 sf⌝ ∗ anyHeap
  onExit := fun _ _ s0 sf => ⌜allocFailedIn s0 sf⌝ ∗ anyHeap
  onOom := fun _ s0 sf => ⌜allocFailedIn s0 sf⌝ ∗ anyHeap

def mainSpecTightPlaced (CodeOk : Memory → Prop) (A : RustAlloc) (stk : Nat) (Statics : SepProp)
    (Run : Inputs → RunAnswer → Prop) : Spec MainGhost where
  pre := fun g s =>
    ⌜CodeOk s.mem ∧ MainCaseB2 Run IsSendOverCap IsStdinOverCap g.i g.r ∧ CliInputsOk g.i ∧
      MainEntryFacts g.i s ∧ stk ≤ s.sp.toNat⌝ ∗
      mainFrame A stk Statics g.i s
  post := fun g s0 sf => ⌜MainPost g.r s0 sf⌝ ∗ stackAt s0.sp stk ∗ anyHeap
  onPanic := fun g s0 sf => ⌜g.r = .abort ∨ allocFailedIn s0 sf⌝ ∗ anyHeap
  onExit := fun _ _ _ _ => ⌜False⌝
  onOom := fun _ _ _ => ⌜False⌝

theorem subroutine_ok_mainSpecPlaced_of_tight {P : Program} {e : BitVec 64}
    {CodeOk : Memory → Prop} {A : RustAlloc} {stk : Nat} {Statics : SepProp}
    {Run : Inputs → RunAnswer → Prop}
    (h : subroutine_ok P e (mainSpecTightPlaced CodeOk A stk Statics Run)) :
    subroutine_ok P e (mainSpecPlaced CodeOk A stk Statics Run) := by
  refine subroutine_ok_mono h
    (fun _ _ _ hp => hp)
    (fun _ _ _ _ hp => ?_)
    (fun _ _ _ _ hp => hp)
    (fun _ _ _ _ _ he => (not_satisfies_false_sepConj he).elim)
    (fun _ _ _ _ ho => (not_satisfies_false_sepConj ho).elim)
  simp only [mainSpecTightPlaced, mainSpecPlaced, sepConj_assoc, satisfies_pure_sepConj] at hp ⊢
  exact ⟨Or.inl hp.1, hp.2⟩

/-- Composes `MuslHarness` with `mainSpecPlaced` once `CodeOk` implies `P.CodeLoaded`. -/
theorem outcome_of_main_placed {elf : ElfImage} {P : Program} {mainPc : BitVec 64}
    {CodeOk : Memory → Prop} {A : RustAlloc} {stk : Nat} {Statics Fr : SepProp}
    {Run : Inputs → RunAnswer → Prop}
    (hE : ElfStaticOk elf)
    (hCode : ∀ m, CodeOk m → P.CodeLoaded m)
    (hH : MuslHarness elf P mainPc Fr
      (fun i => CliInputsOk i ∧ InputsLoadable i) (mainEntryPrePlaced CodeOk A stk Statics))
    (hmain : subroutine_ok P mainPc (mainSpecPlaced CodeOk A stk Statics Run))
    (hstk : 48 ≤ stk) (hstk' : stk ≤ 2 ^ 64)
    {i : Inputs} {r : MainResult} (hi : CliInputsOk i) (hl : InputsLoadable i)
    (hc : MainCaseB2 Run IsSendOverCap IsStdinOverCap i r) :
    (∃ res, outcomeOf elf P (cliInputs i) = some res ∧ MainResult.Observed i.files r res) ∨
    RunAllocFails elf P i := by
  obtain ⟨s0, sm, hload, hsteps0, hpc, hrun, hal, hfs, htr, hx0, hmem, hexit⟩ := hH hE i ⟨hi, hl⟩
  obtain ⟨hfs0, htr0⟩ := loadState_fs_trace hload
  simp only [mainEntryPrePlaced, sepConj_assoc, satisfies_pure_sepConj] at hmem
  obtain ⟨⟨hCO, hsp⟩, hmem⟩ := hmem
  have hpre : sm.mem ⊨ (mainSpecPlaced CodeOk A stk Statics Run).pre ⟨i, r⟩ sm ∗ Fr := by
    simp only [mainSpecPlaced, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hCO, hc, hi, ⟨hx0, hfs.trans hfs0, htr.trans htr0⟩, hsp⟩, hmem⟩
  obtain ⟨sf, hsteps1, hout⟩ := hmain ⟨i, r⟩ Fr sm hpc hrun hpre hal (hCode sm.mem hCO)
  have hsteps01 := hsteps0.trans hsteps1
  have hAF : allocFailedIn sm sf → RunAllocFails elf P i :=
    fun h => ⟨s0, sf, hload, hsteps01, List.mem_of_mem_drop h⟩
  rcases hout with ⟨hret, _, hpost⟩ | ⟨hpan, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, hpost⟩
  · simp only [mainSpecPlaced, sepConj_assoc, satisfies_pure_sepConj] at hpost
    obtain ⟨hφ, hpost⟩ := hpost
    rcases hφ with ⟨code, w, out, rfl, hw0, hfiles, hout⟩ | hA
    · rw [← sepConj_assoc] at hpost
      obtain ⟨sx, hsteps2, hst, hfsx, htrx⟩ :=
        hexit sf hsteps1 hret (exit_frame hstk hstk' hpost)
      have hle := hc.code_le rfl
      refine Or.inl ⟨_, outcomeOf_eq_exited hload (hsteps01.trans hsteps2) hst, ?_⟩
      dsimp only [MainResult.Observed]
      refine ⟨?_, ?_, ?_⟩
      · rw [hw0, signExtend_ofNat_small hle]
      · rw [htrx, hout]
      · rw [hfsx, fsView_congr hfiles, hfs, hfs0]
        exact fsView_writeAll_initFsState i w hc.commitOk
    · exact Or.inr (hAF hA)
  · simp only [mainSpecPlaced, sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost.1 with rfl | hA
    · exact Or.inl ⟨_, outcomeOf_eq_aborted hload hsteps01 hpan, trivial⟩
    · exact Or.inr (hAF hA)
  · simp only [mainSpecPlaced, sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact Or.inr (hAF hpost.1)
  · simp only [mainSpecPlaced, sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact Or.inr (hAF hpost.1)

/-- Composes `MuslHarness` with `mainSpecTightPlaced` (allowing OOM disjunction). -/
theorem outcome_of_main_or_oom_placed {elf : ElfImage} {P : Program} {mainPc : BitVec 64}
    {CodeOk : Memory → Prop} {A : RustAlloc} {stk : Nat} {Statics Fr : SepProp}
    {Run : Inputs → RunAnswer → Prop}
    (hE : ElfStaticOk elf)
    (hCode : ∀ m, CodeOk m → P.CodeLoaded m)
    (hH : MuslHarness elf P mainPc Fr
      (fun i => CliInputsOk i ∧ InputsLoadable i) (mainEntryPrePlaced CodeOk A stk Statics))
    (hmain : subroutine_ok P mainPc (mainSpecTightPlaced CodeOk A stk Statics Run))
    (hstk : 48 ≤ stk) (hstk' : stk ≤ 2 ^ 64)
    {i : Inputs} {r : MainResult} (hi : CliInputsOk i) (hl : InputsLoadable i)
    (hc : MainCaseB2 Run IsSendOverCap IsStdinOverCap i r) :
    (∃ res, outcomeOf elf P (cliInputs i) = some res ∧ MainResult.Observed i.files r res) ∨
    (outcomeOf elf P (cliInputs i) = some .aborted ∧ RunAllocFails elf P i) := by
  obtain ⟨s0, sm, hload, hsteps0, hpc, hrun, hal, hfs, htr, hx0, hmem, hexit⟩ := hH hE i ⟨hi, hl⟩
  obtain ⟨hfs0, htr0⟩ := loadState_fs_trace hload
  simp only [mainEntryPrePlaced, sepConj_assoc, satisfies_pure_sepConj] at hmem
  obtain ⟨⟨hCO, hsp⟩, hmem⟩ := hmem
  have hpre : sm.mem ⊨ (mainSpecTightPlaced CodeOk A stk Statics Run).pre ⟨i, r⟩ sm ∗ Fr := by
    simp only [mainSpecTightPlaced, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hCO, hc, hi, ⟨hx0, hfs.trans hfs0, htr.trans htr0⟩, hsp⟩, hmem⟩
  obtain ⟨sf, hsteps1, hout⟩ := hmain ⟨i, r⟩ Fr sm hpc hrun hpre hal (hCode sm.mem hCO)
  have hsteps01 := hsteps0.trans hsteps1
  have hAF : allocFailedIn sm sf → RunAllocFails elf P i :=
    fun h => ⟨s0, sf, hload, hsteps01, List.mem_of_mem_drop h⟩
  rcases hout with ⟨hret, _, hpost⟩ | ⟨hpan, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, hpost⟩
  · simp only [mainSpecTightPlaced, sepConj_assoc, satisfies_pure_sepConj] at hpost
    obtain ⟨⟨code, w, out, rfl, hw0, hfiles, hout⟩, hpost⟩ := hpost
    rw [← sepConj_assoc] at hpost
    obtain ⟨sx, hsteps2, hst, hfsx, htrx⟩ :=
      hexit sf hsteps1 hret (exit_frame hstk hstk' hpost)
    have hle := hc.code_le rfl
    refine Or.inl ⟨_, outcomeOf_eq_exited hload (hsteps01.trans hsteps2) hst, ?_⟩
    dsimp only [MainResult.Observed]
    refine ⟨?_, ?_, ?_⟩
    · rw [hw0, signExtend_ofNat_small hle]
    · rw [htrx, hout]
    · rw [hfsx, fsView_congr hfiles, hfs, hfs0]
      exact fsView_writeAll_initFsState i w hc.commitOk
  · simp only [mainSpecTightPlaced, sepConj_assoc, satisfies_pure_sepConj] at hpost
    have habort := outcomeOf_eq_aborted hload hsteps01 hpan
    rcases hpost.1 with rfl | hA
    · exact Or.inl ⟨_, habort, trivial⟩
    · exact Or.inr ⟨habort, hAF hA⟩
  · exact (not_satisfies_false_sepConj hpost).elim
  · exact (not_satisfies_false_sepConj hpost).elim

end CryptoVerification.SignalSession.Cli

/-! ## 3. Relocatable PQXDH `IdentityFiles` specifications -/

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate

open Arm64 Arm64.Obj ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.RecordCodecs
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli

def idOwnFutBoxAtPlaced (box self : BitVec 64) (st : BitVec 8) : SepProp :=
  (box ↦₆₄ self) ∗ ((box + 8#64) ↦₈ st) ∗ memRegion (box + 9#64) 7

def idOwnShimSpecPlaced [LibsignalPlacement] (vtSym : String) (A : RustAlloc) (stk : Nat) :
    Spec (BitVec 64) :=
  LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
    { pre := fun self s =>
        ⌜s.readReg64 .x0 = self⌝ ∗ A.pool ∗ stackAt s.sp stk
      post := fun self s0 sf =>
        ⌜sf.readReg64 .x1 = lsρ vtSym ∧ sf.readReg64 .x0 ≠ 0#64 ∧
          (sf.readReg64 .x0).toNat % 8 = 0 ∧ sf.trace = s0.trace⌝ ∗
          A.live (sf.readReg64 .x0) 16 8 ∗
          idOwnFutBoxAtPlaced (sf.readReg64 .x0) self 0#8 ∗
          A.pool ∗ stackAt s0.sp stk
      onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }

structure IdOwnPollGhostPlaced where
  fut : BitVec 64
  out : BitVec 64
  self : BitVec 64
  own : DirGhost

def idKeyPairOutAtPlaced (A : RustAlloc) (out : BitVec 64) :
    Except Unit IdentityKeyPair → SepProp
  | .ok kp =>
    (out ↦₈ 0#8) ∗ ((out + 1#64) ↦ₛ kp.identityKey.publicKey.bytes.toList) ∗
      ((out + 0x21#64) ↦ₛ kp.privateKey.bytes.toList) ∗ memRegion (out + 0x41#64) 7
  | .error () =>
    (out ↦₈ 1#8) ∗ memRegion (out + 1#64) 7 ∗
      (∃∗ k : RunDrop.SpeOwned, RunDrop.speOwnedAt A (out + 8#64) k) ∗
      memRegion (out + 0x38#64) 16

def idKeyPairPollSpecPlaced [LibsignalPlacement] (rd : ReadRule) (pathOk : List (BitVec 8) → Prop)
    (A : RustAlloc) (stk : Nat) : Spec IdOwnPollGhostPlaced :=
  LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.fut ∧ s.readReg64 .x8 = x.out ∧
          x.own.path.length < 2 ^ 32 ∧
          pathOk (pathOf x.own.path (utf8 "identity-key-pair")) ∧
          ∀ bs, x.own.get rd s.fs.files (utf8 "identity-key-pair") = .ok bs →
            bs.length < 2 ^ 32⌝ ∗
          idOwnFutBoxAtPlaced x.fut x.self 0#8 ∗ dirAt A x.self x.own ∗
          memRegion x.out 72 ∗ FromRecordCallees.lsLogOff ∗ A.pool ∗ stackAt s.sp stk
      post := fun x s0 sf =>
        (∃∗ ans : Except Unit IdentityKeyPair,
          ⌜ans = (IdGhost.mk x.own (.new [])).keyPair rd s0.fs.files ∧ sf.trace = s0.trace⌝ ∗
          idKeyPairOutAtPlaced A x.out ans) ∗
          idOwnFutBoxAtPlaced x.fut x.self 1#8 ∗ dirAt A x.self x.own ∗
          FromRecordCallees.lsLogOff ∗ A.pool ∗ stackAt s0.sp stk
      onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }

def idRegIdOutAtPlaced (A : RustAlloc) (out : BitVec 64) : Except Unit (BitVec 32) → SepProp
  | .ok reg =>
    (out ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗ ((out + 8#64) ↦₃₂ reg) ∗ memRegion (out + 12#64) 36
  | .error () => ∃∗ k : RunDrop.SpeOwned, RunDrop.speOwnedAt A out k

def idRegIdPollSpecPlaced [LibsignalPlacement] (rd : ReadRule) (pathOk : List (BitVec 8) → Prop)
    (A : RustAlloc) (stk : Nat) : Spec IdOwnPollGhostPlaced :=
  LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.fut ∧ s.readReg64 .x8 = x.out ∧
          x.own.path.length < 2 ^ 32 ∧
          pathOk (pathOf x.own.path (utf8 "registration-id"))⌝ ∗
          idOwnFutBoxAtPlaced x.fut x.self 0#8 ∗ dirAt A x.self x.own ∗
          memRegion x.out 48 ∗ A.pool ∗ stackAt s.sp stk
      post := fun x s0 sf =>
        (∃∗ ans : Except Unit (BitVec 32),
          ⌜ans = (IdGhost.mk x.own (.new [])).regId rd s0.fs.files ∧ sf.trace = s0.trace⌝ ∗
          idRegIdOutAtPlaced A x.out ans) ∗
          idOwnFutBoxAtPlaced x.fut x.self 1#8 ∗ dirAt A x.self x.own ∗
          A.pool ∗ stackAt s0.sp stk
      onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate

/-! ## 4. Relocatable `Main` layout, callees, I/O, and `runSpecPlaced` -/

namespace CryptoVerification.SignalSession.Cli.MainHops

open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Main.Placed

noncomputable abbrev mProgPlaced [LibsignalPlacement] (H : LibsignalHooks) : Program :=
  lsProg_617 H

noncomputable abbrev mPcPlaced [LibsignalPlacement] (k : Nat) : BitVec 64 :=
  lsmpl.base 617 + BitVec.ofNat 64 k

def coinsInstalledPlaced [LibsignalPlacement] (p : BitVec 64) (coins : List (BitVec 8)) : SepProp :=
  (Coins.coinsNextPlaced ↦₆₄ p) ∗
    (Coins.coinsLeftPlaced ↦₆₄ BitVec.ofNat 64 coins.length) ∗ (p ↦ₛ coins)

abbrev coinsLitSym : String := "libsignal_cli:.rodata..Lanon.97"

def dirLitsPlaced : List (String × String) :=
  [("libsignal_cli:.rodata..Lanon.51", "identities"),
   ("libsignal_cli:.rodata..Lanon.46", "signed-pre-keys"),
   ("libsignal_cli:.rodata..Lanon.48", "one-time-kyber-pre-keys"),
   ("libsignal_cli:.rodata..Lanon.49", "last-resort-kyber-pre-keys"),
   ("libsignal_cli:.rodata..Lanon.47", "one-time-pre-keys"),
   ("libsignal_cli:.rodata.cst8", "sessions"),
   ("libsignal_cli:.rodata..Lanon.53", "public")]

def mainLitsPlaced [LibsignalPlacement] : SepProp :=
  (lsρ coinsLitSym ↦ᵣ utf8 "coins") ∗
    (dirLitsPlaced.foldr (fun l P => (lsρ l.1 ↦ᵣ utf8 l.2) ∗ P) emp)

/-- Relocatable 14-field allocator and `libc` memory contract bundle on `lsProg_617 H` (`withLsCodeRoLoaded`). -/
structure AllocContractsXCliPlaced [LibsignalPlacement] (A : RustAlloc)
    (H : LibsignalHooks) : Prop where
  alloc : subroutine_ok (lsProg_617 H) (lsρ lsRustAllocSymCli)
    (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (rustAllocSpecWithStack A extHookStack))
  dealloc : subroutine_ok (lsProg_617 H) (lsρ lsRustDeallocSymCli)
    (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (rustDeallocExternSpecWithStack A extHookStack))
  realloc : subroutine_ok (lsProg_617 H) (lsρ lsRustReallocSymCli)
    (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (rustReallocExternSpecWithStack A extHookStack))
  shim : ∀ (stk : Nat), extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    subroutine_ok (lsProg_617 H) (lsρ lsRustNoAllocShimSymCli)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (withStack sessionShimSpec stk))
  memcpy : ∀ (stk : Nat), extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    subroutine_ok (lsProg_617 H) (lsρ memcpyName)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (libcMemcpySpec stk))
  session_memcpy : ∀ (stk : Nat), extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    subroutine_ok (lsProg_617 H) (lsρ memcpyName)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (sessionMemcpySpec stk))
  memcpy_region : ∀ (stk : Nat), extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    subroutine_ok (lsProg_617 H) (lsρ memcpyName)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (withStack memcpyRegionSpec stk))
  session_memcpy_region : ∀ (stk : Nat), extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    subroutine_ok (lsProg_617 H) (lsρ memcpyName)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (withStack sessionMemcpyRegionSpec stk))
  memmove : ∀ (stk : Nat), extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    subroutine_ok (lsProg_617 H) (lsρ memmoveName)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (libcMemmoveSpec stk))
  session_memmove : ∀ (stk : Nat), extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    subroutine_ok (lsProg_617 H) (lsρ memmoveName)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (sessionMemmoveSpec stk))
  memset : ∀ (stk : Nat), extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    subroutine_ok (lsProg_617 H) (lsρ memsetName)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (libcMemsetSpec stk))
  session_memset : ∀ (stk : Nat), extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    subroutine_ok (lsProg_617 H) (lsρ memsetName)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (sessionMemsetSpec stk))
  memset_region : ∀ (stk : Nat), extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    subroutine_ok (lsProg_617 H) (lsρ memsetName)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (withStack memsetRegionSpec stk))
  session_memset_region : ∀ (stk : Nat), extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    subroutine_ok (lsProg_617 H) (lsρ memsetName)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (withStack sessionMemsetRegionSpec stk))

/-- Relocatable 15-field `.keepsFs` allocator and `libc` memory contract bundle on `lsProg_617 H`. -/
structure AllocContractsFsPlaced [LibsignalPlacement] (A : RustAlloc)
    (H : LibsignalHooks) : Prop where
  alloc : subroutine_ok (lsProg_617 H) (lsρ lsRustAllocSymCli)
    (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (rustAllocSpecWithStack A extHookStack).keepsFs)
  dealloc : subroutine_ok (lsProg_617 H) (lsρ lsRustDeallocSymCli)
    (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (rustDeallocExternSpecWithStack A extHookStack).keepsFs)
  realloc : subroutine_ok (lsProg_617 H) (lsρ lsRustReallocSymCli)
    (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (rustReallocExternSpecWithStack A extHookStack).keepsFs)
  shim : ∀ (stk : Nat), extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    subroutine_ok (lsProg_617 H) (lsρ lsRustNoAllocShimSymCli)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (withStack sessionShimSpec stk).keepsFs)
  memcpy : ∀ (stk : Nat), extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    subroutine_ok (lsProg_617 H) (lsρ memcpyName)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (libcMemcpySpec stk).keepsFs)
  session_memcpy : ∀ (stk : Nat), extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    subroutine_ok (lsProg_617 H) (lsρ memcpyName)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (sessionMemcpySpec stk).keepsFs)
  memcpy_region : ∀ (stk : Nat), extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    subroutine_ok (lsProg_617 H) (lsρ memcpyName)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (withStack memcpyRegionSpec stk).keepsFs)
  session_memcpy_region : ∀ (stk : Nat), extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    subroutine_ok (lsProg_617 H) (lsρ memcpyName)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (withStack sessionMemcpyRegionSpec stk).keepsFs)
  memmove : ∀ (stk : Nat), extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    subroutine_ok (lsProg_617 H) (lsρ memmoveName)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (libcMemmoveSpec stk).keepsFs)
  session_memmove : ∀ (stk : Nat), extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    subroutine_ok (lsProg_617 H) (lsρ memmoveName)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (sessionMemmoveSpec stk).keepsFs)
  memset : ∀ (stk : Nat), extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    subroutine_ok (lsProg_617 H) (lsρ memsetName)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (libcMemsetSpec stk).keepsFs)
  session_memset : ∀ (stk : Nat), extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    subroutine_ok (lsProg_617 H) (lsρ memsetName)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (sessionMemsetSpec stk).keepsFs)
  memset_region : ∀ (stk : Nat), extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    subroutine_ok (lsProg_617 H) (lsρ memsetName)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (withStack memsetRegionSpec stk).keepsFs)
  session_memset_region : ∀ (stk : Nat), extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    subroutine_ok (lsProg_617 H) (lsρ memsetName)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (withStack sessionMemsetRegionSpec stk).keepsFs)
  session_memcpy_region_ro : ∀ (stk : Nat), extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    subroutine_ok (lsProg_617 H) (lsρ memcpyName)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (withStack CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpec stk).keepsFs)

/-- Relocatable direct callee contracts of `main` (Block `617`): Blocks `580`, `588`, and `561`. -/
structure MainCalleesPlaced [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks)
    (uuidParse : UuidParser) (hookStack resStack : Nat) : Prop where
  alloc : AllocContractsXCliPlaced A H
  allocFs : AllocContractsFsPlaced A H
  strlen : subroutine_ok (lsProg_617 H) (lsρ "strlen")
    (withLsRoCl lsmpl (strlenSpec hookStack))
  fromUtf8 : subroutine_ok (lsProg_617 H) (lsρ lsFromUtf8Sym)
    (withLsRoCl lsmpl (fromUtf8AsciiSpec hookStack))
  address : subroutine_ok (lsProg_617 H) (lsmpl.base 580)
    (withLsRoCl lsmpl (addressSpec A uuidParse resStack))
  reserve16 : subroutine_ok (lsProg_617 H) (lsmpl.base 588)
    (withLsRoCl lsmpl (reserve16Spec A resStack))
  reserve1 : subroutine_ok (lsProg_617 H) (lsmpl.base 588)
    (withLsRoCl lsmpl
      (CryptoVerification.SpqrV1.Varint.doReserveSpecOf resStack A).keepsFs)
  tryAllocateIn3 : subroutine_ok (lsProg_617 H) (lsmpl.base 561)
    (withLsRoCl lsmpl (tryAllocateInSpecOf resStack A).keepsFs)

def readStdinSpecPlaced (io : IoModel) (A : RustAlloc) (stk : Nat) : Spec ReadStdinGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x8 = x.ret ∧ io.stdin s.fs = some x.bs⌝ ∗
      memRegion x.ret 24 ∗ stackAt s.sp stk ∗ A.pool
  post := fun x s0 sf =>
    (∃∗ r : Except Unit (List (BitVec 8)),
      ⌜sf.fs.files = s0.fs.files ∧ r = readStdinResult x.bs ∧ sf.trace = s0.trace⌝ ∗
        ioVecAt A x.ret r) ∗
      stackAt s0.sp stk ∗ A.pool
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

def readFileLitSpecPlaced (io : IoModel) (A : RustAlloc) (stk : Nat) : Spec ReadFileLitGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.pathA ∧ (s.readReg64 .x1).toNat = x.path.length ∧
      s.readReg64 .x8 = x.ret ∧ x.path.length < 2 ^ 32 ∧ io.pathOk x.path⌝ ∗
      (x.pathA ↦ᵣ x.path) ∗ memRegion x.ret 24 ∗ stackAt s.sp stk ∗ A.pool
  post := fun x s0 sf =>
    (∃∗ r : Except Unit (List (BitVec 8)),
      ⌜sf.fs.files = s0.fs.files ∧ r = io.rd s0.fs.files x.path ∧ sf.trace = s0.trace⌝ ∗
        ioVecAt A x.ret r) ∗
      (x.pathA ↦ᵣ x.path) ∗ stackAt s0.sp stk ∗ A.pool
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

def writeFileSpecPlaced (io : IoModel) (stk : Nat) : Spec WriteFileGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.pathA ∧ (s.readReg64 .x1).toNat = x.path.length ∧
      s.readReg64 .x2 = x.buf ∧ (s.readReg64 .x3).toNat = x.bs.length ∧
      x.path.length < 2 ^ 32 ∧ io.pathOk x.path⌝ ∗
      (x.pathA ↦ₛ x.path) ∗ (x.buf ↦ₛ x.bs) ∗ stackAt s.sp stk
  post := fun x s0 sf =>
    ⌜(match io.wr s0.fs.files x.path x.bs with
      | some F' => sf.readReg64 .x0 = 0#64 ∧ sf.fs.files = F'
      | none => sf.readReg64 .x0 = 1#64 ∧ sf.fs.files = s0.fs.files) ∧
      s0.trace <+: sf.trace ∧
      ProcessOutcome.traceStreamBytes .stdout sf.trace =
        ProcessOutcome.traceStreamBytes .stdout s0.trace⌝ ∗
      (x.pathA ↦ₛ x.path) ∗ (x.buf ↦ₛ x.bs) ∗ stackAt s0.sp stk

def writeStdoutSpecPlaced (stk : Nat) : Spec WriteStdoutGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.buf ∧ (s.readReg64 .x1).toNat = x.bs.length⌝ ∗
      (x.buf ↦ₛ x.bs) ∗ stackAt s.sp stk
  post := fun x s0 sf =>
    ⌜sf.readReg64 .x0 = 0#64 ∧ sf.fs.files = s0.fs.files ∧ s0.trace <+: sf.trace ∧
      ProcessOutcome.traceStreamBytes .stdout sf.trace =
        ProcessOutcome.traceStreamBytes .stdout s0.trace ++ x.bs⌝ ∗
      (x.buf ↦ₛ x.bs) ∗ stackAt s0.sp stk

/-- Relocatable I/O contracts of `main` on Block `617` (`lsProg_617 H`). -/
structure MainIoPlaced [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks)
    (io : IoModel) (hookStack : Nat) : Prop where
  readStdin : subroutine_ok (lsProg_617 H) (lsρ lsReadStdinSym)
    (withLsRoCl lsmpl (readStdinSpecPlaced io A hookStack))
  readFile : subroutine_ok (lsProg_617 H) (lsρ lsReadFileSym)
    (withLsRoCl lsmpl (readFileLitSpecPlaced io A hookStack))
  writeFile : subroutine_ok (lsProg_617 H) (lsρ lsWriteFileSym)
    (withLsRoCl lsmpl (writeFileSpecPlaced io hookStack))
  writeStdout : subroutine_ok (lsProg_617 H) (lsρ lsWriteStdoutSym)
    (withLsRoCl lsmpl (writeStdoutSpecPlaced hookStack))

/-- Relocatable `signal_session::run` (Block `579`) specification parameterized by `CodeOk : Memory → Prop`. -/
def runSpecPlaced [LibsignalPlacement] (CodeOk : Memory → Prop) (A : RustAlloc)
    (uuidParse : UuidParser) (Run : Inputs → RunAnswer → Prop)
    (wrOk : List (BitVec 8) → Prop) (resStack : Nat) : Spec RunCall where
  pre := fun g s0 =>
    ⌜CodeOk s0.mem ∧ Run g.i g.a ∧ parseArgs uuidParse (g.i.argv.map bytesOfString) = some g.c ∧
      s0.readReg64 .x0 = g.res ∧ s0.readReg64 .x1 = g.call ∧ s0.readReg64 .x2 = g.stores ∧
      s0.readReg64 .x3 = g.inp ∧
      s0.readReg64 .x4 = BitVec.ofNat 64 (inputOf g.i g.c).length ∧
      s0.fs.files = (initFsState (cliInputs g.i)).files ∧
      ProcessOutcome.traceStreamBytes .stdout s0.trace = [] ∧ resStack ≤ s0.sp.toNat⌝ ∗
      memRegion g.res runResSize ∗ callAt A g.call g.c ∗ storesAt A g.stores StoresGhost.opened ∗
      (g.inp ↦ₛ inputOf g.i g.c) ∗ coinsInstalledPlaced g.coins (coinsOf g.i) ∗
      SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗
      FromRecordCallees.lsLogOff ∗ A.pool ∗ stackAt s0.sp resStack
  post := fun g s0 sf =>
    ⌜s0.trace <+: sf.trace ∧
      sf.fs.files = s0.fs.files ∧
      ProcessOutcome.traceStreamBytes .stdout sf.trace =
        ProcessOutcome.traceStreamBytes .stdout s0.trace⌝ ∗
      memRegion g.call 56 ∗ memRegion g.stores 320 ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
      A.pool ∗ stackAt s0.sp resStack ∗
      (∃∗ a' : RunAnswer, ⌜a' ≠ none ∧ a' = g.a⌝ ∗
        runResAt A wrOk g.res a') ∗ anyHeap
  onPanic := fun g s0 sf => ⌜g.a = none ∨ allocFailedIn s0 sf⌝ ∗ anyHeap

end CryptoVerification.SignalSession.Cli.MainHops
