/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.PureBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.CalleesBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.TopBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlaced
public import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarintPlacedCommonBudget
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Process

/-!
# Budget-Threaded Relocatable CLI Specifications and Process Composition

Defines `RustCliAllocBudget M`-threaded `[LibsignalPlacement]` counterparts of the CLI function,
store shim/poll, `main` entry/process composition, PQXDH `IdentityFiles`, and `MainHops`
specifications, parameterized by `BudgetLimits` and callee `AllocEvent` envelopes.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

open scoped CryptoVerification.RustHeap
open CryptoGames.LibsignalSession (IdentityKey SignalProtocolError)
open CryptoGames.LibsignalSessionApi (SessionRecord)
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl lsρ)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open CryptoVerification.E2E.Record (encodeRecord recDeserializeStack)
open CryptoVerification.E2E.Record.DeserializeGeneral (DeserializeGenGhost)
open CryptoVerification.E2E.Record.Serialization (CanonRecord)
open CryptoVerification.LibsignalPublicApi.StoreSession (StoreShimCall)
open CryptoVerification.LibsignalPublicApiRepr (RecordGhost sessionRecordAt)
open CryptoVerification.LibsignalTripleRatchet (extHookStack lsLogOff memcpyName memmoveName memsetName withStack)
open CryptoVerification.LibsignalTripleRatchet.Getters (dropSpeStackX)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost UuidParser protocolAddressAt speWord)
open CryptoVerification.RecordCodecs (IdentityKeyPair KyberPreKeyRecord)
open CryptoVerification.RecordCodecsBinary (preKeyResultAt signedPreKeyResultAt)
open CryptoVerification.RustHeap (allocFailedIn vecU8)
open CryptoVerification.SignalSession (Inputs lsFromUtf8Sym lsReadFileSym lsReadStdinSym lsRustAllocSymCli lsRustDeallocSymCli lsRustNoAllocShimSymCli lsRustReallocSymCli lsWriteFileSym lsWriteStdoutSym outcomeOf outcomeOf_eq_aborted outcomeOf_eq_exited)
open CryptoVerification.SignalSession.Cli (AddrTextGhost BundleReadGhost CliInputsOk DecimalGhost DirGetGhost DirGhost DirPutGhost DirPutStrGhost DropSpeWordGhost ElfStaticOk GrowOneDirGhost IdFileWf IdPeerAns IdPollGhost InputsLoadable IsSendOverCap IsStdinOverCap KpkBaseKeysOk KpkMarkAns KpkMarkPollGhost KpkMarkShimCall KpkPollGhost KpkSeenOk KyberGhost MainCaseB2 MainEntryFacts MainGhost MainPost MainResult MuslHarness PathGhost PkAns PkNameOk PkPollGhost PkShimCall PkSizeOk ReadFileGhost ReadRule RunAllocFails RunAnswer SessFileWf SessLoadAns SessLoadPollGhost SessStorePollGhost SplitGhost addressText cliInputs decimalText dirAt exit_frame fsView_congr fsView_writeAll_initFsState getResultAt idSaveBoxAt idSaveFutVtSym idSaveOf idSaveOutAt idSavePeers idTrustBoxAt idTrustFutVtSym idTrustOf idTrustOutAt ioVecAt keyName kpkAnsAt kpkAnsOf kpkMarkBoxAt kpkMarkFutVtSym kpkMarkOf kpkMarkOutAt loadState_fs_trace pathOf pkAnsAt pkAnsOf pkBoxAt pkRemoveOf pkRemoveOutAt sessLoadBoxAt sessLoadFutVtSym sessLoadOutAt sessStoreBoxAt sessStoreFutVtSym signExtend_ofNat_small splitIdResultAt splitSignedResultAt)
open CryptoVerification.SignalSession.Cli.Main.Placed (lsProg_617)
open CryptoVerification.SignalSession.Cli.MainHops (IoModel ReadFileLitGhost ReadStdinGhost RunCall WriteFileGhost WriteStdoutGhost callAt coinsInstalledPlaced coinsOf fromUtf8AsciiSpec inputOf parseArgs runResAt runResSize storesAt strlenSpec)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate (IdOwnPollGhostPlaced idKeyPairOutAtPlaced idOwnFutBoxAtPlaced idRegIdOutAtPlaced)
open CryptoVerification.SpqrV1.Alloc (sessionMemcpyRegionROSpec)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)

namespace LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget

open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoVerification.LibsignalPublicApi.StoreKit
  (FsFiles IdentityShimCall LoadShimCall withLsRoCl)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget rustDeallocEvents)
open LibsignalBinary.Heap.SpecBudget
  (ReadFileEnv ReadStdinEnv WriteFileEnv WriteStdoutEnv allocBytes1Events cliIoCapsEvents
   cliIoReadScheduleCaps withVmPreserved)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (BoxAllocEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.PureBudget (growOneDirRawSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.CalleesBudget
  (addressSpec reserve16Spec tryAllocateInSpecOf)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.TopBudget (mainFrame)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarintPlacedCommonBudget (doReserveSpecOf)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
  (sessionMemcpyBudgetSpec sessionMemcpyRegionBudgetSpec sessionMemmoveBudgetSpec
   sessionMemsetBudgetSpec sessionMemsetRegionBudgetSpec sessionShimBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget
  (rustAllocSpecWithStack rustDeallocExternSpecWithStack rustReallocExternSpecWithStack)

/-! ## 1. `ReadFileRuleEnv`, `path`, and `decimal` -/

/-- `ReadRule`-parameterized `read_file` allocator event envelope covering both hook
`allocBytes1Events` and the compiled doubling schedule `cliIoReadScheduleCaps 9`. -/
def ReadFileRuleEnv (rd : ReadRule) (files : FsFiles) (path : List (BitVec 8))
    (evs : List AllocEvent) : Prop :=
  match rd files path with
  | .ok bs =>
    evs = allocBytes1Events bs ∨
    ((4096 ≤ path.length ∨ 0#8 ∈ path) ∧ evs = []) ∨
    (bs.length ≤ 2097152 ∧ evs = cliIoCapsEvents 0 (cliIoReadScheduleCaps 9 bs.length)) ∨
    (2097152 < bs.length ∧
      evs = cliIoCapsEvents 0 (cliIoReadScheduleCaps 9 2097152) ++ rustDeallocEvents 2097152 1)
  | .error () => evs = []

theorem readFileRuleEnv_eq_readFileEnv :
    ReadFileRuleEnv CryptoVerification.SignalSession.CliExt.readFileResult = ReadFileEnv :=
  rfl

def pathSpecPlaced [LibsignalPlacement] {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits)
    (PathEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop)
    (stk : Nat) : Spec (PathGhost × M.σ) :=
  CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
    { pre := fun (x, st) s =>
        ⌜s.readReg64 .x0 = x.ret ∧ s.readReg64 .x1 = x.dirA ∧
          (s.readReg64 .x2).toNat = x.dir.length ∧ s.readReg64 .x3 = x.nameA ∧
          (s.readReg64 .x4).toNat = x.name.length ∧
          x.dir.length < 2 ^ 32 ∧ x.name.length < 2 ^ 32 ∧
          FitsEnv M lim st (PathEnv x.dir x.name)⌝ ∗
          CryptoVerification.SpqrV1.ChainProofs.bytesAt x.dirRo x.dirA x.dir ∗
          CryptoVerification.SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗ memRegion x.ret 24 ∗
          stackAt s.sp stk ∗ A.pool lim st s
      post := fun (x, st) s0 sf =>
        ∃∗ evs : List AllocEvent,
          ⌜sf.trace = s0.trace ∧ PathEnv x.dir x.name evs⌝ ∗
            vecU8 A.repAlloc x.ret (x.dir ++ [0x2f#8] ++ x.name) ∗
            CryptoVerification.SpqrV1.ChainProofs.bytesAt x.dirRo x.dirA x.dir ∗
            CryptoVerification.SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
            stackAt s0.sp stk ∗ A.pool lim (M.stepEvents evs st) sf }

def decimalSpecPlaced [LibsignalPlacement] {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (DecEnv : BitVec 32 → List AllocEvent → Prop)
    (stk : Nat) : Spec (DecimalGhost × M.σ) :=
  CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
    { pre := fun (x, st) s =>
        ⌜s.readReg64 .x0 = x.ret ∧ s.readReg32 .x1 = x.n ∧
          FitsEnv M lim st (DecEnv x.n)⌝ ∗
          memRegion x.ret 24 ∗ stackAt s.sp stk ∗ A.pool lim st s
      post := fun (x, st) s0 sf =>
        ∃∗ evs : List AllocEvent,
          ⌜sf.trace = s0.trace ∧ DecEnv x.n evs⌝ ∗
            vecU8 A.repAlloc x.ret (decimalText x.n.toNat) ∗
            stackAt s0.sp stk ∗ A.pool lim (M.stepEvents evs st) sf }

/-! ## 2. Directory helpers (`read_file`, `address_text`, `grow_one`, `Dir::put`, `Dir::get`) -/

/-- Budget-threaded hook-level `read_file` specification (without `inImage` or `withLsCodeRoLoaded`). -/
def readFileSpecPlaced {M : AllocCostModel} (rd : ReadRule) (pathOk : List (BitVec 8) → Prop)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop := ReadFileRuleEnv rd) :
    Spec (ReadFileGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.pathA ∧ (s.readReg64 .x1).toNat = x.path.length ∧
      s.readReg64 .x8 = x.ret ∧ x.path.length < 2 ^ 32 ∧ pathOk x.path ∧
      FitsEnv M lim st (ReadEnv s.fs.files x.path)⌝ ∗
      (x.pathA ↦ₛ x.path) ∗ memRegion x.ret 24 ∗ stackAt s.sp stk ∗ A.pool lim st s
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜ReadEnv s0.fs.files x.path evs⌝ ∗
        (∃∗ r : Except Unit (List (BitVec 8)),
          ⌜r = rd s0.fs.files x.path ∧ sf.trace = s0.trace⌝ ∗ ioVecAt A.repAlloc x.ret r) ∗
        (x.pathA ↦ₛ x.path) ∗ stackAt s0.sp stk ∗ A.pool lim (M.stepEvents evs st) sf

def addrTextSpecPlaced [LibsignalPlacement] {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (AddrEnv : AddrGhost → List AllocEvent → Prop)
    (stk : Nat) : Spec (AddrTextGhost × M.σ) :=
  CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
    { pre := fun (x, st) s =>
        ⌜s.readReg64 .x0 = x.ret ∧ s.readReg64 .x1 = x.addr ∧ x.g.name.bytes.length < 2 ^ 32 ∧
          FitsEnv M lim st (AddrEnv x.g) ∧ LsRetAddr624 (s.readReg64 .x30)⌝ ∗
          protocolAddressAt A.repAlloc x.g x.addr ∗ memRegion x.ret 24 ∗
          stackAt s.sp stk ∗ A.pool lim st s
      post := fun (x, st) s0 sf =>
        ∃∗ evs : List AllocEvent,
          ⌜sf.trace = s0.trace ∧ AddrEnv x.g evs⌝ ∗
            vecU8 A.repAlloc x.ret (addressText x.g.val) ∗
            protocolAddressAt A.repAlloc x.g x.addr ∗
            stackAt s0.sp stk ∗ A.pool lim (M.stepEvents evs st) sf }

/-- Relocatable `RawVec<(String, Vec<u8>)>::grow_one` specification wrapped in `withLsCodeRoLoaded lsmpl`. -/
def growOneDirSpecPlaced [LibsignalPlacement] {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (stk : Nat) : Spec (GrowOneDirGhost × M.σ) :=
  CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (growOneDirRawSpec A lim stk)

def dirPutSpecPlaced [LibsignalPlacement] {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits)
    (PutEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop)
    (stk : Nat) : Spec (DirPutGhost × M.σ) :=
  CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
    { pre := fun (x, st) s =>
        ⌜s.readReg64 .x0 = x.self ∧ s.readReg64 .x1 = x.nameV ∧ s.readReg64 .x2 = x.bytesV ∧
          x.dir.changed.length < 2 ^ 32 ∧
          FitsEnv M lim st (PutEnv x.dir x.name x.bytes) ∧
          LsRetAddr624 (s.readReg64 .x30)⌝ ∗
          dirAt A.repAlloc x.self x.dir ∗
          vecU8 A.repAlloc x.nameV x.name ∗ vecU8 A.repAlloc x.bytesV x.bytes ∗
          stackAt s.sp stk ∗ A.pool lim st s
      post := fun (x, st) s0 sf =>
        ∃∗ evs : List AllocEvent,
          ⌜sf.trace = s0.trace ∧ PutEnv x.dir x.name x.bytes evs⌝ ∗
            dirAt A.repAlloc x.self (x.dir.put x.name x.bytes) ∗
            memRegion x.nameV 24 ∗ memRegion x.bytesV 24 ∗
            stackAt s0.sp stk ∗ A.pool lim (M.stepEvents evs st) sf }

def dirPutStrSpecPlaced [LibsignalPlacement] {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits)
    (PutStrEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop)
    (stk : Nat) : Spec (DirPutStrGhost × M.σ) :=
  CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
    { pre := fun (x, st) s =>
        ⌜s.readReg64 .x0 = x.self ∧ s.readReg64 .x1 = x.nameA ∧
          (s.readReg64 .x2).toNat = x.name.length ∧ s.readReg64 .x3 = x.bytesV ∧
          x.name.length < 2 ^ 32 ∧ x.dir.changed.length < 2 ^ 32 ∧
          FitsEnv M lim st (PutStrEnv x.dir x.name x.bytes) ∧
          LsRetAddr624 (s.readReg64 .x30)⌝ ∗
          dirAt A.repAlloc x.self x.dir ∗ CryptoVerification.SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
          vecU8 A.repAlloc x.bytesV x.bytes ∗ stackAt s.sp stk ∗ A.pool lim st s
      post := fun (x, st) s0 sf =>
        ∃∗ evs : List AllocEvent,
          ⌜sf.trace = s0.trace ∧ PutStrEnv x.dir x.name x.bytes evs⌝ ∗
            dirAt A.repAlloc x.self (x.dir.put x.name x.bytes) ∗
            CryptoVerification.SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗ memRegion x.bytesV 24 ∗
            stackAt s0.sp stk ∗ A.pool lim (M.stepEvents evs st) sf }

def dirGetSpecPlaced [LibsignalPlacement] {M : AllocCostModel} (rd : ReadRule)
    (pathOk : List (BitVec 8) → Prop) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop)
    (stk : Nat) : Spec (DirGetGhost × M.σ) :=
  CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
    { pre := fun (x, st) s =>
        ⌜s.readReg64 .x0 = x.ret ∧ s.readReg64 .x1 = x.self ∧ s.readReg64 .x2 = x.nameA ∧
          (s.readReg64 .x3).toNat = x.name.length ∧ x.name.length < 2 ^ 32 ∧
          x.dir.path.length < 2 ^ 32 ∧ pathOk (pathOf x.dir.path x.name) ∧
          FitsEnv M lim st (GetEnv s.fs.files x.dir x.name)⌝ ∗
          dirAt A.repAlloc x.self x.dir ∗ CryptoVerification.SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
          memRegion x.ret 48 ∗ stackAt s.sp stk ∗ A.pool lim st s
      post := fun (x, st) s0 sf =>
        ∃∗ evs : List AllocEvent,
          (∃∗ r : Except Unit (List (BitVec 8)),
            ⌜r = x.dir.get rd s0.fs.files x.name ∧ sf.trace = s0.trace ∧
              GetEnv s0.fs.files x.dir x.name evs⌝ ∗
              getResultAt A.repAlloc x.ret r) ∗
            dirAt A.repAlloc x.self x.dir ∗ CryptoVerification.SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
            stackAt s0.sp stk ∗ A.pool lim (M.stepEvents evs st) sf }

/-! ## 3. Bundle helpers (`split_id`, `split_signed`, `read_bundle::{closure#0}`) -/

def splitIdSpecPlaced [LibsignalPlacement] {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (SplitEnv : List (BitVec 8) → List AllocEvent → Prop)
    (stk : Nat) : Spec (SplitGhost × M.σ) :=
  CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
    { pre := fun (x, st) s =>
        ⌜s.readReg64 .x0 = x.ret ∧ s.readReg64 .x1 = x.fp ∧
          (s.readReg64 .x2).toNat = x.file.length ∧
          FitsEnv M lim st (SplitEnv x.file)⌝ ∗
          CryptoVerification.SpqrV1.ChainProofs.bytesAt x.ro x.fp x.file ∗ memRegion x.ret 48 ∗
          stackAt s.sp stk ∗ A.pool lim st s
      post := fun (x, st) s0 sf =>
        ∃∗ evs : List AllocEvent,
          ⌜sf.trace = s0.trace ∧ SplitEnv x.file evs⌝ ∗
            splitIdResultAt A.repAlloc x.ret x.fp x.file ∗
            CryptoVerification.SpqrV1.ChainProofs.bytesAt x.ro x.fp x.file ∗
            stackAt s0.sp stk ∗ A.pool lim (M.stepEvents evs st) sf }

def splitSignedSpecPlaced [LibsignalPlacement] {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (SplitEnv : List (BitVec 8) → List AllocEvent → Prop)
    (stk : Nat) : Spec (SplitGhost × M.σ) :=
  CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
    { pre := fun (x, st) s =>
        ⌜s.readReg64 .x0 = x.ret ∧ s.readReg64 .x1 = x.fp ∧
          (s.readReg64 .x2).toNat = x.file.length ∧
          FitsEnv M lim st (SplitEnv x.file)⌝ ∗
          CryptoVerification.SpqrV1.ChainProofs.bytesAt x.ro x.fp x.file ∗ memRegion x.ret 48 ∗
          stackAt s.sp stk ∗ A.pool lim st s
      post := fun (x, st) s0 sf =>
        ∃∗ evs : List AllocEvent,
          ⌜sf.trace = s0.trace ∧ SplitEnv x.file evs⌝ ∗
            splitSignedResultAt A.repAlloc x.ret x.fp x.file ∗
            CryptoVerification.SpqrV1.ChainProofs.bytesAt x.ro x.fp x.file ∗
            stackAt s0.sp stk ∗ A.pool lim (M.stepEvents evs st) sf }

def bundleReadSpecPlaced [LibsignalPlacement] {M : AllocCostModel} (rd : ReadRule)
    (pathOk : List (BitVec 8) → Prop) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (BundleEnv : FsFiles → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop)
    (stk : Nat) : Spec (BundleReadGhost × M.σ) :=
  CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
    { pre := fun (x, st) s =>
        ⌜s.readReg64 .x0 = x.ret ∧ s.readReg64 .x1 = x.dirA ∧
          (s.readReg64 .x2).toNat = x.dir.length ∧ s.readReg64 .x3 = x.nameA ∧
          (s.readReg64 .x4).toNat = x.name.length ∧ x.dir.length < 2 ^ 32 ∧
          x.name.length < 2 ^ 32 ∧ pathOk (x.dir ++ [0x2f#8] ++ x.name) ∧
          FitsEnv M lim st (BundleEnv s.fs.files x.dir x.name)⌝ ∗
          CryptoVerification.SpqrV1.ChainProofs.bytesAt x.dirRo x.dirA x.dir ∗
          CryptoVerification.SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗ memRegion x.ret 48 ∗
          stackAt s.sp stk ∗ A.pool lim st s
      post := fun (x, st) s0 sf =>
        ∃∗ evs : List AllocEvent,
          (∃∗ r : Except Unit (List (BitVec 8)),
            ⌜r = rd s0.fs.files (x.dir ++ [0x2f#8] ++ x.name) ∧ sf.trace = s0.trace ∧
              BundleEnv s0.fs.files x.dir x.name evs⌝ ∗
              getResultAt A.repAlloc x.ret r) ∗
            CryptoVerification.SpqrV1.ChainProofs.bytesAt x.dirRo x.dirA x.dir ∗
            CryptoVerification.SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
            stackAt s0.sp stk ∗ A.pool lim (M.stepEvents evs st) sf }

/-! ## 4. Store shim and poll specifications -/

def sessLoadShimSpecPlaced [LibsignalPlacement] {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (stk : Nat) : Spec (LoadShimCall × M.σ) :=
  CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
    { pre := fun (x, st) s =>
        ⌜s.readReg64 .x0 = x.self ∧ s.readReg64 .x1 = x.addrA ∧
          FitsEnv M lim st (BoxAllocEnv 24)⌝ ∗
          A.pool lim st s ∗ stackAt s.sp stk
      post := fun (x, st) s0 sf =>
        ∃∗ evs : List AllocEvent,
          ⌜sf.readReg64 .x1 = lsρ sessLoadFutVtSym ∧ sf.readReg64 .x0 ≠ 0#64 ∧
            (sf.readReg64 .x0).toNat % 8 = 0 ∧ sf.trace = s0.trace ∧
            BoxAllocEnv 24 evs⌝ ∗
            A.live (sf.readReg64 .x0) 24 8 ∗
            sessLoadBoxAt (sf.readReg64 .x0) x.self x.addrA 0#8 ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp stk }

def sessStoreShimSpecPlaced [LibsignalPlacement] {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (stk : Nat) : Spec (StoreShimCall × M.σ) :=
  CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
    { pre := fun (x, st) s =>
        ⌜s.readReg64 .x0 = x.self ∧ s.readReg64 .x1 = x.addrA ∧ s.readReg64 .x2 = x.recA ∧
          FitsEnv M lim st (BoxAllocEnv 32)⌝ ∗
          A.pool lim st s ∗ stackAt s.sp stk
      post := fun (x, st) s0 sf =>
        ∃∗ evs : List AllocEvent,
          ⌜sf.readReg64 .x1 = lsρ sessStoreFutVtSym ∧ sf.readReg64 .x0 ≠ 0#64 ∧
            (sf.readReg64 .x0).toNat % 8 = 0 ∧ sf.trace = s0.trace ∧
            BoxAllocEnv 32 evs⌝ ∗
            A.live (sf.readReg64 .x0) 32 8 ∗
            sessStoreBoxAt (sf.readReg64 .x0) x.self x.addrA x.recA 0#8 ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp stk }

noncomputable def sessDeserializeSpecPlaced [LibsignalPlacement] {M : AllocCostModel}
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (A : RustCliAllocBudget M)
    (lim : BudgetLimits)
    (DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop) :
    Spec (DeserializeGenGhost × M.σ) :=
  CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
    { pre := fun (x, st) s =>
        ⌜s.readReg64 .x0 = x.p ∧
          s.readReg64 .x1 = BitVec.ofNat 64 (encodeRecord x.r).length ∧
          s.readReg64 .x8 = x.out ∧ Scope x.r ∧
          FitsEnv M lim st (DeserEnv x.r)⌝ ∗
          (x.p ↦ₛ encodeRecord x.r) ∗ memRegion x.out 368 ∗
          A.pool lim st s ∗ stackAt s.sp recDeserializeStack
      post := fun (x, st) s0 sf =>
        ∃∗ evs : List AllocEvent,
          ⌜sf.trace = s0.trace ∧ DeserEnv x.r evs⌝ ∗
            (x.p ↦ₛ encodeRecord x.r) ∗
            (∃∗ g : RecordGhost, ⌜CanonRecord g x.r⌝ ∗
              CryptoVerification.E2E.Record.sessionRecordAt A.repAlloc x.out g x.r) ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp recDeserializeStack }

def sessLoadPollSpecPlaced [LibsignalPlacement] {M : AllocCostModel} (rd : ReadRule)
    (pathOk : List (BitVec 8) → Prop) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (LoadEnv : FsFiles → SessLoadPollGhost → List AllocEvent → Prop)
    (stk : Nat) : Spec (SessLoadPollGhost × M.σ) :=
  CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
    { pre := fun (x, st) s =>
        ⌜s.readReg64 .x0 = x.call.fut ∧ s.readReg64 .x8 = x.call.out ∧
          x.call.addr.name.bytes.length < 2 ^ 32 ∧
          (addressText x.call.addr.val).length < 2 ^ 32 ∧ x.dir.path.length < 2 ^ 32 ∧
          pathOk (pathOf x.dir.path (addressText x.call.addr.val)) ∧
          (∀ bs, x.dir.get rd s.fs.files (addressText x.call.addr.val) = .ok bs →
            SessFileWf Scope bs) ∧
          FitsEnv M lim st (LoadEnv s.fs.files x)⌝ ∗
          sessLoadBoxAt x.call.fut x.self x.call.addrA 0#8 ∗ dirAt A.repAlloc x.self x.dir ∗
          memRegion x.call.out 368 ∗ protocolAddressAt A.repAlloc x.call.addr x.call.addrA ∗
          A.pool lim st s ∗ stackAt s.sp stk
      post := fun (x, st) s0 sf =>
        ∃∗ evs : List AllocEvent,
          (∃∗ gr : Except Unit (List (BitVec 8)),
            ∃∗ ans : Except Unit (Option (SessionRecord (List (BitVec 8)))),
            ⌜(gr = x.dir.get rd s0.fs.files (addressText x.call.addr.val) ∧ sf.trace = s0.trace) ∧
              SessLoadAns Scope gr ans ∧ LoadEnv s0.fs.files x evs⌝ ∗
            sessLoadOutAt A.repAlloc x.call.out ans) ∗
            sessLoadBoxAt x.call.fut x.self x.call.addrA 1#8 ∗ dirAt A.repAlloc x.self x.dir ∗
            protocolAddressAt A.repAlloc x.call.addr x.call.addrA ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp stk }

def sessStorePollSpecPlaced [LibsignalPlacement] {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (StoreEnv : SessStorePollGhost → List AllocEvent → Prop)
    (stk : Nat) : Spec (SessStorePollGhost × M.σ) :=
  CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
    { pre := fun (x, st) s =>
        ⌜s.readReg64 .x0 = x.call.fut ∧ s.readReg64 .x8 = x.call.out ∧
          x.call.call.addr.name.bytes.length < 2 ^ 32 ∧
          (encodeRecord x.call.call.record).length < 2 ^ 32 ∧
          x.dir.changed.length < 2 ^ 32 ∧
          FitsEnv M lim st (StoreEnv x)⌝ ∗
          sessStoreBoxAt x.call.fut x.self x.call.call.addrA x.call.call.recA 0#8 ∗
          dirAt A.repAlloc x.self x.dir ∗ memRegion x.call.out 48 ∗
          protocolAddressAt A.repAlloc x.call.call.addr x.call.call.addrA ∗
          sessionRecordAt A.repAlloc x.call.call.recA x.call.call.g x.call.call.record ∗
          A.pool lim st s ∗ stackAt s.sp stk
      post := fun (x, st) s0 sf =>
        ∃∗ evs : List AllocEvent,
          ⌜sf.trace = s0.trace ∧ StoreEnv x evs⌝ ∗
            sessStoreBoxAt x.call.fut x.self x.call.call.addrA x.call.call.recA 1#8 ∗
            dirAt A.repAlloc x.self (x.dir.put (addressText x.call.call.addr.val)
              (encodeRecord x.call.call.record)) ∗
            (x.call.out ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗ memRegion (x.call.out + 8#64) 40 ∗
            protocolAddressAt A.repAlloc x.call.call.addr x.call.call.addrA ∗
            sessionRecordAt A.repAlloc x.call.call.recA x.call.call.g x.call.call.record ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp stk }

def idSaveShimSpecPlaced [LibsignalPlacement] {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (stk : Nat) : Spec (IdentityShimCall × M.σ) :=
  CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
    { pre := fun (x, st) s =>
        ⌜s.readReg64 .x0 = x.self ∧ s.readReg64 .x1 = x.addrA ∧ s.readReg64 .x2 = x.keyA ∧
          FitsEnv M lim st (BoxAllocEnv 32)⌝ ∗
          A.pool lim st s ∗ stackAt s.sp stk
      post := fun (x, st) s0 sf =>
        ∃∗ evs : List AllocEvent,
          ⌜sf.readReg64 .x1 = lsρ idSaveFutVtSym ∧ sf.readReg64 .x0 ≠ 0#64 ∧
            (sf.readReg64 .x0).toNat % 8 = 0 ∧ sf.trace = s0.trace ∧
            BoxAllocEnv 32 evs⌝ ∗
            A.live (sf.readReg64 .x0) 32 8 ∗
            idSaveBoxAt (sf.readReg64 .x0) x.self x.addrA x.keyA 0#8 ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp stk }

def idTrustShimSpecPlaced [LibsignalPlacement] {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (stk : Nat) : Spec ((IdentityShimCall × BitVec 8) × M.σ) :=
  CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
    { pre := fun ((x, d), st) s =>
        ⌜s.readReg64 .x0 = x.self ∧ s.readReg64 .x1 = x.addrA ∧ s.readReg64 .x2 = x.keyA ∧
          (s.readReg64 .x3).setWidth 8 = d ∧
          FitsEnv M lim st (BoxAllocEnv 32)⌝ ∗
          A.pool lim st s ∗ stackAt s.sp stk
      post := fun ((x, d), st) s0 sf =>
        ∃∗ evs : List AllocEvent,
          ⌜sf.readReg64 .x1 = lsρ idTrustFutVtSym ∧ sf.readReg64 .x0 ≠ 0#64 ∧
            (sf.readReg64 .x0).toNat % 8 = 0 ∧ sf.trace = s0.trace ∧
            BoxAllocEnv 32 evs⌝ ∗
            A.live (sf.readReg64 .x0) 32 8 ∗
            idTrustBoxAt (sf.readReg64 .x0) x.self x.addrA x.keyA 0#8 d ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp stk }

def idTrustPollSpecPlaced [LibsignalPlacement] {M : AllocCostModel} (rd : ReadRule)
    (pathOk : List (BitVec 8) → Prop) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (TrustEnv : FsFiles → IdPollGhost → List AllocEvent → Prop)
    (stk : Nat) : Spec ((IdPollGhost × BitVec 8) × M.σ) :=
  CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
    { pre := fun ((x, d), st) s =>
        ⌜s.readReg64 .x0 = x.call.fut ∧ s.readReg64 .x8 = x.call.out ∧
          x.call.call.addr.name.bytes.length < 2 ^ 32 ∧ x.peers.path.length < 2 ^ 32 ∧
          pathOk (pathOf x.peers.path x.call.call.addr.val.name) ∧
          (∀ bs, x.peers.get rd s.fs.files x.call.call.addr.val.name = .ok bs → IdFileWf bs) ∧
          FitsEnv M lim st (TrustEnv s.fs.files x)⌝ ∗
          idTrustBoxAt x.call.fut x.self x.call.call.addrA x.call.call.keyA 0#8 d ∗
          dirAt A.repAlloc (x.self + 0x28#64) x.peers ∗ memRegion x.call.out 48 ∗
          protocolAddressAt A.repAlloc x.call.call.addr x.call.call.addrA ∗
          (x.call.call.keyA ↦ₛ x.call.call.key.publicKey.bytes.toList) ∗
          lsLogOff ∗ A.pool lim st s ∗ stackAt s.sp stk
      post := fun ((x, d), st) s0 sf =>
        ∃∗ evs : List AllocEvent,
          (∃∗ gr : Except Unit (List (BitVec 8)),
            ∃∗ p : Except Unit (Option IdentityKey),
            ⌜(gr = x.peers.get rd s0.fs.files x.call.call.addr.val.name ∧ sf.trace = s0.trace) ∧
              IdPeerAns gr p ∧ TrustEnv s0.fs.files x evs⌝ ∗
            idTrustOutAt A.repAlloc x.call.out (idTrustOf p x.call.call.key)) ∗
            idTrustBoxAt x.call.fut x.self x.call.call.addrA x.call.call.keyA 1#8 d ∗
            dirAt A.repAlloc (x.self + 0x28#64) x.peers ∗
            protocolAddressAt A.repAlloc x.call.call.addr x.call.call.addrA ∗
            (x.call.call.keyA ↦ₛ x.call.call.key.publicKey.bytes.toList) ∗
            lsLogOff ∗ A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp stk }

def idSavePollSpecPlaced [LibsignalPlacement] {M : AllocCostModel} (rd : ReadRule)
    (pathOk : List (BitVec 8) → Prop) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (SaveEnv : FsFiles → IdPollGhost → List AllocEvent → Prop)
    (stk : Nat) : Spec (IdPollGhost × M.σ) :=
  CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
    { pre := fun (x, st) s =>
        ⌜s.readReg64 .x0 = x.call.fut ∧ s.readReg64 .x8 = x.call.out ∧
          x.call.call.addr.name.bytes.length < 2 ^ 32 ∧ x.peers.path.length < 2 ^ 32 ∧
          x.peers.changed.length < 2 ^ 32 ∧
          pathOk (pathOf x.peers.path x.call.call.addr.val.name) ∧
          (∀ bs, x.peers.get rd s.fs.files x.call.call.addr.val.name = .ok bs → IdFileWf bs) ∧
          FitsEnv M lim st (SaveEnv s.fs.files x)⌝ ∗
          idSaveBoxAt x.call.fut x.self x.call.call.addrA x.call.call.keyA 0#8 ∗
          dirAt A.repAlloc (x.self + 0x28#64) x.peers ∗ memRegion x.call.out 48 ∗
          protocolAddressAt A.repAlloc x.call.call.addr x.call.call.addrA ∗
          (x.call.call.keyA ↦ₛ x.call.call.key.publicKey.bytes.toList) ∗
          lsLogOff ∗ A.pool lim st s ∗ stackAt s.sp stk
      post := fun (x, st) s0 sf =>
        ∃∗ evs : List AllocEvent,
          (∃∗ gr : Except Unit (List (BitVec 8)),
            ∃∗ p : Except Unit (Option IdentityKey),
            ⌜(gr = x.peers.get rd s0.fs.files x.call.call.addr.val.name ∧ sf.trace = s0.trace) ∧
              IdPeerAns gr p ∧ SaveEnv s0.fs.files x evs⌝ ∗
            idSaveOutAt A.repAlloc x.call.out (idSaveOf p x.call.call.key) ∗
            dirAt A.repAlloc (x.self + 0x28#64)
              (idSavePeers x.peers x.call.call.addr.val.name x.call.call.key p)) ∗
            idSaveBoxAt x.call.fut x.self x.call.call.addrA x.call.call.keyA 1#8 ∗
            protocolAddressAt A.repAlloc x.call.call.addr x.call.call.addrA ∗
            (x.call.call.keyA ↦ₛ x.call.call.key.publicKey.bytes.toList) ∗
            lsLogOff ∗ A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp stk }

def pkShimSpecPlaced [LibsignalPlacement] {M : AllocCostModel} (vtSym : String)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat) : Spec (PkShimCall × M.σ) :=
  CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
    { pre := fun (x, st) s =>
        ⌜s.readReg64 .x0 = x.self ∧ s.readReg32 .x1 = x.id ∧
          FitsEnv M lim st (BoxAllocEnv 16)⌝ ∗
          A.pool lim st s ∗ stackAt s.sp stk
      post := fun (x, st) s0 sf =>
        ∃∗ evs : List AllocEvent,
          ⌜sf.readReg64 .x1 = lsρ vtSym ∧ sf.readReg64 .x0 ≠ 0#64 ∧
            (sf.readReg64 .x0).toNat % 8 = 0 ∧ sf.trace = s0.trace ∧
            BoxAllocEnv 16 evs⌝ ∗
            A.live (sf.readReg64 .x0) 16 8 ∗ pkBoxAt (sf.readReg64 .x0) x.self x.id 0#8 ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp stk }

def kpkMarkShimSpecPlaced [LibsignalPlacement] {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (stk : Nat) : Spec (KpkMarkShimCall × M.σ) :=
  CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
    { pre := fun (x, st) s =>
        ⌜s.readReg64 .x0 = x.self ∧ s.readReg32 .x1 = x.id ∧ s.readReg32 .x2 = x.signedId ∧
          s.readReg64 .x3 = x.baseKeyA ∧
          FitsEnv M lim st (BoxAllocEnv 32)⌝ ∗
          A.pool lim st s ∗ stackAt s.sp stk
      post := fun (x, st) s0 sf =>
        ∃∗ evs : List AllocEvent,
          ⌜sf.readReg64 .x1 = lsρ kpkMarkFutVtSym ∧ sf.readReg64 .x0 ≠ 0#64 ∧
            (sf.readReg64 .x0).toNat % 8 = 0 ∧ sf.trace = s0.trace ∧
            BoxAllocEnv 32 evs⌝ ∗
            A.live (sf.readReg64 .x0) 32 8 ∗
            kpkMarkBoxAt (sf.readReg64 .x0) x.self x.baseKeyA x.id x.signedId 0#8 ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp stk }

def pkGetPollSpecOfPlaced [LibsignalPlacement] {α : Type} {M : AllocCostModel}
    (dec : List (BitVec 8) → Except SignalProtocolError α)
    (resAt : CryptoVerification.RustHeap.RustAlloc → BitVec 64 →
      Except SignalProtocolError α → SepProp) (size w : Nat)
    (rd : ReadRule) (pathOk : List (BitVec 8) → Prop) (A : RustCliAllocBudget M)
    (lim : BudgetLimits)
    (PollEnv : FsFiles → PkPollGhost → List AllocEvent → Prop)
    (stk : Nat) : Spec (PkPollGhost × M.σ) :=
  CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
    { pre := fun (x, st) s =>
        ⌜s.readReg64 .x0 = x.fut ∧ s.readReg64 .x8 = x.out ∧ PkNameOk pathOk x.dir x.id ∧
          PkSizeOk rd s.fs.files x.dir x.id ∧
          FitsEnv M lim st (PollEnv s.fs.files x)⌝ ∗
          pkBoxAt x.fut x.self x.id 0#8 ∗ dirAt A.repAlloc x.self x.dir ∗ memRegion x.out size ∗
          A.pool lim st s ∗ stackAt s.sp stk
      post := fun (x, st) s0 sf =>
        ∃∗ evs : List AllocEvent,
          (∃∗ ans : PkAns α,
            ⌜ans = pkAnsOf dec (x.dir.get rd s0.fs.files (keyName x.id)) ∧ sf.trace = s0.trace ∧
              PollEnv s0.fs.files x evs⌝ ∗
            pkAnsAt A.repAlloc resAt size w x.out ans) ∗
            pkBoxAt x.fut x.self x.id 1#8 ∗ dirAt A.repAlloc x.self x.dir ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp stk }

abbrev spkGetPollSpecPlaced [LibsignalPlacement] {M : AllocCostModel} (rd : ReadRule)
    (pathOk : List (BitVec 8) → Prop) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (PollEnv : FsFiles → PkPollGhost → List AllocEvent → Prop)
    (stk : Nat) : Spec (PkPollGhost × M.σ) :=
  pkGetPollSpecOfPlaced CryptoVerification.RecordCodecs.SignedPreKeyRecord.deserialize signedPreKeyResultAt 88 14 rd pathOk A lim
    PollEnv stk

abbrev pkGetPollSpecPlaced [LibsignalPlacement] {M : AllocCostModel} (rd : ReadRule)
    (pathOk : List (BitVec 8) → Prop) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (PollEnv : FsFiles → PkPollGhost → List AllocEvent → Prop)
    (stk : Nat) : Spec (PkPollGhost × M.σ) :=
  pkGetPollSpecOfPlaced CryptoVerification.RecordCodecs.PreKeyRecord.deserialize preKeyResultAt 56 13 rd pathOk A lim PollEnv stk

def pkRemovePollSpecPlaced [LibsignalPlacement] {M : AllocCostModel} (rd : ReadRule)
    (pathOk : List (BitVec 8) → Prop) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (RemEnv : FsFiles → PkPollGhost → List AllocEvent → Prop)
    (stk : Nat) : Spec (PkPollGhost × M.σ) :=
  CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
    { pre := fun (x, st) s =>
        ⌜s.readReg64 .x0 = x.fut ∧ s.readReg64 .x8 = x.out ∧ PkNameOk pathOk x.dir x.id ∧
          x.dir.changed.length < 2 ^ 32 ∧
          FitsEnv M lim st (RemEnv s.fs.files x)⌝ ∗
          pkBoxAt x.fut x.self x.id 0#8 ∗ dirAt A.repAlloc x.self x.dir ∗ memRegion x.out 48 ∗
          A.pool lim st s ∗ stackAt s.sp stk
      post := fun (x, st) s0 sf =>
        ∃∗ evs : List AllocEvent,
          (∃∗ res : Except Unit Unit × DirGhost,
            ⌜res = pkRemoveOf x.dir (keyName x.id) (x.dir.get rd s0.fs.files (keyName x.id)) ∧
              sf.trace = s0.trace ∧ RemEnv s0.fs.files x evs⌝ ∗
            pkRemoveOutAt A.repAlloc x.out res.1 ∗ dirAt A.repAlloc x.self res.2) ∗
            pkBoxAt x.fut x.self x.id 1#8 ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp stk }

def kpkGetPollSpecPlaced [LibsignalPlacement] {M : AllocCostModel} (rd : ReadRule)
    (pathOk : List (BitVec 8) → Prop) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (PollEnv : FsFiles → KpkPollGhost → List AllocEvent → Prop)
    (stk : Nat) : Spec (KpkPollGhost × M.σ) :=
  CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
    { pre := fun (x, st) s =>
        ⌜s.readReg64 .x0 = x.fut ∧ s.readReg64 .x8 = x.out ∧
          PkNameOk pathOk x.kg.oneTime x.id ∧ PkNameOk pathOk x.kg.lastResort x.id ∧
          PkSizeOk rd s.fs.files x.kg.oneTime x.id ∧ PkSizeOk rd s.fs.files x.kg.lastResort x.id ∧
          FitsEnv M lim st (PollEnv s.fs.files x)⌝ ∗
          pkBoxAt x.fut x.self x.id 0#8 ∗ dirAt A.repAlloc x.self x.kg.oneTime ∗
          dirAt A.repAlloc (x.self + 0x28#64) x.kg.lastResort ∗ memRegion x.out 88 ∗
          A.pool lim st s ∗ stackAt s.sp stk
      post := fun (x, st) s0 sf =>
        ∃∗ evs : List AllocEvent,
          (∃∗ ans : PkAns KyberPreKeyRecord,
            ⌜ans = kpkAnsOf
                  (pkAnsOf CryptoVerification.RecordCodecs.KyberPreKeyRecord.deserialize
                    (x.kg.oneTime.get rd s0.fs.files (keyName x.id)))
                  (pkAnsOf CryptoVerification.RecordCodecs.KyberPreKeyRecord.deserialize
                    (x.kg.lastResort.get rd s0.fs.files (keyName x.id))) ∧
              sf.trace = s0.trace ∧ PollEnv s0.fs.files x evs⌝ ∗
            kpkAnsAt A.repAlloc x.out ans) ∗
            pkBoxAt x.fut x.self x.id 1#8 ∗ dirAt A.repAlloc x.self x.kg.oneTime ∗
            dirAt A.repAlloc (x.self + 0x28#64) x.kg.lastResort ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp stk }

def dropSpeWordSpecPlaced [LibsignalPlacement] {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (DropSpeWordGhost × M.σ) :=
  CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
    { pre := fun (x, st) s =>
        ⌜s.readReg64 .x0 = x.a ∧ (x.w = 13 ∨ x.w = 14)⌝ ∗
          (x.a ↦₆₄ speWord x.w) ∗ memRegion (x.a + 8#64) 40 ∗ A.pool lim st s ∗
          stackAt s.sp dropSpeStackX
      post := fun (x, st) s0 sf =>
        ⌜sf.trace = s0.trace⌝ ∗ memRegion x.a 48 ∗ A.pool lim st sf ∗
          stackAt s0.sp dropSpeStackX }

def kpkMarkPollSpecPlaced [LibsignalPlacement] {M : AllocCostModel} (rd : ReadRule)
    (pathOk : List (BitVec 8) → Prop) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (MarkEnv : FsFiles → KpkMarkPollGhost → List AllocEvent → Prop)
    (stk : Nat) : Spec (KpkMarkPollGhost × M.σ) :=
  CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
    { pre := fun (x, st) s =>
        ⌜s.readReg64 .x0 = x.fut ∧ s.readReg64 .x8 = x.out ∧
          PkNameOk pathOk x.kg.oneTime x.id ∧ KpkBaseKeysOk pathOk x.kg.lastResort x.id ∧
          KpkSeenOk rd s.fs.files x.kg.lastResort x.id x.signedId x.baseKey ∧
          x.kg.oneTime.changed.length < 2 ^ 32 ∧ x.kg.lastResort.changed.length < 2 ^ 32 ∧
          FitsEnv M lim st (MarkEnv s.fs.files x)⌝ ∗
          kpkMarkBoxAt x.fut x.self x.baseKeyA x.id x.signedId 0#8 ∗
          dirAt A.repAlloc x.self x.kg.oneTime ∗
          dirAt A.repAlloc (x.self + 0x28#64) x.kg.lastResort ∗
          (x.baseKeyA ↦ₛ x.baseKey.bytes.toList) ∗ memRegion x.out 48 ∗
          A.pool lim st s ∗ stackAt s.sp stk
      post := fun (x, st) s0 sf =>
        ∃∗ evs : List AllocEvent,
          (∃∗ res : KpkMarkAns × KyberGhost,
            ⌜res = kpkMarkOf rd s0.fs.files x.kg x.id x.signedId x.baseKey ∧
              sf.trace = s0.trace ∧ MarkEnv s0.fs.files x evs⌝ ∗
            kpkMarkOutAt A.repAlloc x.out res.1 ∗
            dirAt A.repAlloc x.self res.2.oneTime ∗
            dirAt A.repAlloc (x.self + 0x28#64) res.2.lastResort) ∗
            kpkMarkBoxAt x.fut x.self x.baseKeyA x.id x.signedId 1#8 ∗
            (x.baseKeyA ↦ₛ x.baseKey.bytes.toList) ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp stk }

/-! ## 5. `main` entry precondition and process composition -/

def mainEntryPrePlaced (CodeOk : Memory → Prop) {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (stk : Nat) (Statics : SepProp)
    (i : Inputs) (s : State) : SepProp :=
  ⌜CodeOk s.mem ∧ stk ≤ s.sp.toNat⌝ ∗ mainFrame A lim st stk Statics i s

def mainSpecPlaced (CodeOk : Memory → Prop) {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (stk : Nat) (Statics : SepProp)
    (Run : Inputs → RunAnswer → Prop) : Spec (MainGhost × M.σ) where
  pre := fun (g, st) s =>
    ⌜CodeOk s.mem ∧ MainCaseB2 Run IsSendOverCap IsStdinOverCap g.i g.r ∧ CliInputsOk g.i ∧ MainEntryFacts g.i s ∧
      stk ≤ s.sp.toNat⌝ ∗
      mainFrame A lim st stk Statics g.i s
  post := fun (g, _) s0 sf =>
    ⌜MainPost g.r s0 sf ∨ allocFailedIn s0 sf⌝ ∗ stackAt s0.sp stk ∗ anyHeap
  onPanic := fun (g, _) s0 sf => ⌜g.r = .abort ∨ allocFailedIn s0 sf⌝ ∗ anyHeap
  onExit := fun _ _ s0 sf => ⌜allocFailedIn s0 sf⌝ ∗ anyHeap
  onOom := fun _ s0 sf => ⌜allocFailedIn s0 sf⌝ ∗ anyHeap

def mainSpecPlacedAt (CodeOk : Memory → Prop) {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (stk : Nat) (Statics : SepProp)
    (Run : Inputs → RunAnswer → Prop) : Spec MainGhost where
  pre := fun g s =>
    ⌜CodeOk s.mem ∧ MainCaseB2 Run IsSendOverCap IsStdinOverCap g.i g.r ∧ CliInputsOk g.i ∧ MainEntryFacts g.i s ∧
      stk ≤ s.sp.toNat⌝ ∗
      mainFrame A lim st stk Statics g.i s
  post := fun g s0 sf =>
    ⌜MainPost g.r s0 sf ∨ allocFailedIn s0 sf⌝ ∗ stackAt s0.sp stk ∗ anyHeap
  onPanic := fun g s0 sf => ⌜g.r = .abort ∨ allocFailedIn s0 sf⌝ ∗ anyHeap
  onExit := fun _ _ s0 sf => ⌜allocFailedIn s0 sf⌝ ∗ anyHeap
  onOom := fun _ s0 sf => ⌜allocFailedIn s0 sf⌝ ∗ anyHeap

def mainSpecTightPlaced (CodeOk : Memory → Prop) {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (stk : Nat) (Statics : SepProp)
    (Run : Inputs → RunAnswer → Prop) : Spec (MainGhost × M.σ) where
  pre := fun (g, st) s =>
    ⌜CodeOk s.mem ∧ MainCaseB2 Run IsSendOverCap IsStdinOverCap g.i g.r ∧ CliInputsOk g.i ∧ MainEntryFacts g.i s ∧
      stk ≤ s.sp.toNat⌝ ∗
      mainFrame A lim st stk Statics g.i s
  post := fun (g, _) s0 sf => ⌜MainPost g.r s0 sf⌝ ∗ stackAt s0.sp stk ∗ anyHeap
  onPanic := fun (g, _) s0 sf => ⌜g.r = .abort ∨ allocFailedIn s0 sf⌝ ∗ anyHeap
  onExit := fun _ _ _ _ => ⌜False⌝
  onOom := fun _ _ _ => ⌜False⌝

def mainSpecTightPlacedAt (CodeOk : Memory → Prop) {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (stk : Nat) (Statics : SepProp)
    (Run : Inputs → RunAnswer → Prop) : Spec MainGhost where
  pre := fun g s =>
    ⌜CodeOk s.mem ∧ MainCaseB2 Run IsSendOverCap IsStdinOverCap g.i g.r ∧ CliInputsOk g.i ∧ MainEntryFacts g.i s ∧
      stk ≤ s.sp.toNat⌝ ∗
      mainFrame A lim st stk Statics g.i s
  post := fun g s0 sf => ⌜MainPost g.r s0 sf⌝ ∗ stackAt s0.sp stk ∗ anyHeap
  onPanic := fun g s0 sf => ⌜g.r = .abort ∨ allocFailedIn s0 sf⌝ ∗ anyHeap
  onExit := fun _ _ _ _ => ⌜False⌝
  onOom := fun _ _ _ => ⌜False⌝

theorem subroutine_ok_mainSpecPlaced_of_tight {P : Program} {e : BitVec 64}
    {CodeOk : Memory → Prop} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {stk : Nat} {Statics : SepProp} {Run : Inputs → RunAnswer → Prop}
    (h : subroutine_ok P e (mainSpecTightPlaced CodeOk A lim stk Statics Run)) :
    subroutine_ok P e (mainSpecPlaced CodeOk A lim stk Statics Run) := by
  refine subroutine_ok_mono h
    (fun _ _ _ hp => hp)
    (fun _ _ _ _ hp => ?_)
    (fun _ _ _ _ hp => hp)
    (fun _ _ _ _ _ he => (not_satisfies_false_sepConj he).elim)
    (fun _ _ _ _ ho => (not_satisfies_false_sepConj ho).elim)
  simp only [mainSpecTightPlaced, mainSpecPlaced, sepConj_assoc, satisfies_pure_sepConj] at hp ⊢
  exact ⟨Or.inl hp.1, hp.2⟩

theorem outcome_of_main_placed {elf : ElfImage} {P : Program} {mainPc : BitVec 64}
    {CodeOk : Memory → Prop} {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {st : M.σ} {stk : Nat} {Statics Fr : SepProp}
    {Run : Inputs → RunAnswer → Prop}
    (hE : ElfStaticOk elf)
    (hCode : ∀ m, CodeOk m → P.CodeLoaded m)
    (hH : MuslHarness elf P mainPc Fr
      (fun i => CliInputsOk i ∧ InputsLoadable i) (mainEntryPrePlaced CodeOk A lim st stk Statics))
    (hmain : subroutine_ok P mainPc (mainSpecPlaced CodeOk A lim stk Statics Run))
    (hstk : 48 ≤ stk) (hstk' : stk ≤ 2 ^ 64)
    {i : Inputs} {r : MainResult} (hi : CliInputsOk i) (hl : InputsLoadable i)
    (hc : MainCaseB2 Run IsSendOverCap IsStdinOverCap i r) :
    (∃ res, outcomeOf elf P (cliInputs i) = some res ∧ CryptoVerification.SignalSession.Cli.MainResult.Observed i.files r res) ∨
    RunAllocFails elf P i := by
  obtain ⟨s0, sm, hload, hsteps0, hpc, hrun, hal, hfs, htr, hx0, hmem, hexit⟩ := hH hE i ⟨hi, hl⟩
  obtain ⟨hfs0, htr0⟩ := loadState_fs_trace hload
  simp only [mainEntryPrePlaced, sepConj_assoc, satisfies_pure_sepConj] at hmem
  obtain ⟨⟨hCO, hsp⟩, hmem⟩ := hmem
  have hpre : sm.mem ⊨ (mainSpecPlaced CodeOk A lim stk Statics Run).pre (⟨i, r⟩, st) sm ∗ Fr := by
    simp only [mainSpecPlaced, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hCO, hc, hi, ⟨hx0, hfs.trans hfs0, htr.trans htr0⟩, hsp⟩, hmem⟩
  obtain ⟨sf, hsteps1, hout, _⟩ :=
    hmain.no_fault_before_outcome (⟨i, r⟩, st) Fr sm hpc hrun hpre hal (hCode sm.mem hCO)
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
      dsimp only [CryptoVerification.SignalSession.Cli.MainResult.Observed]
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

theorem outcome_of_main_or_oom_placed {elf : ElfImage} {P : Program} {mainPc : BitVec 64}
    {CodeOk : Memory → Prop} {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {st : M.σ} {stk : Nat} {Statics Fr : SepProp}
    {Run : Inputs → RunAnswer → Prop}
    (hE : ElfStaticOk elf)
    (hCode : ∀ m, CodeOk m → P.CodeLoaded m)
    (hH : MuslHarness elf P mainPc Fr
      (fun i => CliInputsOk i ∧ InputsLoadable i) (mainEntryPrePlaced CodeOk A lim st stk Statics))
    (hmain : subroutine_ok P mainPc (mainSpecTightPlaced CodeOk A lim stk Statics Run))
    (hstk : 48 ≤ stk) (hstk' : stk ≤ 2 ^ 64)
    {i : Inputs} {r : MainResult} (hi : CliInputsOk i) (hl : InputsLoadable i)
    (hc : MainCaseB2 Run IsSendOverCap IsStdinOverCap i r) :
    (∃ res, outcomeOf elf P (cliInputs i) = some res ∧ CryptoVerification.SignalSession.Cli.MainResult.Observed i.files r res) ∨
    (outcomeOf elf P (cliInputs i) = some .aborted ∧ RunAllocFails elf P i) := by
  obtain ⟨s0, sm, hload, hsteps0, hpc, hrun, hal, hfs, htr, hx0, hmem, hexit⟩ := hH hE i ⟨hi, hl⟩
  obtain ⟨hfs0, htr0⟩ := loadState_fs_trace hload
  simp only [mainEntryPrePlaced, sepConj_assoc, satisfies_pure_sepConj] at hmem
  obtain ⟨⟨hCO, hsp⟩, hmem⟩ := hmem
  have hpre : sm.mem ⊨ (mainSpecTightPlaced CodeOk A lim stk Statics Run).pre (⟨i, r⟩, st) sm ∗ Fr := by
    simp only [mainSpecTightPlaced, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hCO, hc, hi, ⟨hx0, hfs.trans hfs0, htr.trans htr0⟩, hsp⟩, hmem⟩
  obtain ⟨sf, hsteps1, hout, _⟩ :=
    hmain.no_fault_before_outcome (⟨i, r⟩, st) Fr sm hpc hrun hpre hal (hCode sm.mem hCO)
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
    dsimp only [CryptoVerification.SignalSession.Cli.MainResult.Observed]
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

/-! ## 6. Relocatable PQXDH `IdentityFiles` specifications -/

def idOwnShimSpecPlaced [LibsignalPlacement] {M : AllocCostModel} (vtSym : String)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat) : Spec (BitVec 64 × M.σ) :=
  CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
    { pre := fun (self, st) s =>
        ⌜s.readReg64 .x0 = self ∧ FitsEnv M lim st (BoxAllocEnv 16)⌝ ∗
          A.pool lim st s ∗ stackAt s.sp stk
      post := fun (self, st) s0 sf =>
        ∃∗ evs : List AllocEvent,
          ⌜sf.readReg64 .x1 = lsρ vtSym ∧ sf.readReg64 .x0 ≠ 0#64 ∧
            (sf.readReg64 .x0).toNat % 8 = 0 ∧ sf.trace = s0.trace ∧
            BoxAllocEnv 16 evs⌝ ∗
            A.live (sf.readReg64 .x0) 16 8 ∗
            idOwnFutBoxAtPlaced (sf.readReg64 .x0) self 0#8 ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp stk }

def idKeyPairPollSpecPlaced [LibsignalPlacement] {M : AllocCostModel} (rd : ReadRule)
    (pathOk : List (BitVec 8) → Prop) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (PollEnv : FsFiles → IdOwnPollGhostPlaced → List AllocEvent → Prop)
    (stk : Nat) : Spec (IdOwnPollGhostPlaced × M.σ) :=
  CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
    { pre := fun (x, st) s =>
        ⌜s.readReg64 .x0 = x.fut ∧ s.readReg64 .x8 = x.out ∧
          x.own.path.length < 2 ^ 32 ∧
          pathOk (pathOf x.own.path (CryptoVerification.SignalSession.Cli.utf8 "identity-key-pair")) ∧
          (∀ bs, x.own.get rd s.fs.files (CryptoVerification.SignalSession.Cli.utf8 "identity-key-pair") = .ok bs →
            bs.length < 2 ^ 32) ∧
          FitsEnv M lim st (PollEnv s.fs.files x)⌝ ∗
          idOwnFutBoxAtPlaced x.fut x.self 0#8 ∗ dirAt A.repAlloc x.self x.own ∗
          memRegion x.out 72 ∗ lsLogOff ∗ A.pool lim st s ∗ stackAt s.sp stk
      post := fun (x, st) s0 sf =>
        ∃∗ evs : List AllocEvent,
          (∃∗ ans : Except Unit IdentityKeyPair,
            ⌜ans = (CryptoVerification.SignalSession.Cli.IdGhost.mk x.own (.new [])).keyPair rd s0.fs.files ∧ sf.trace = s0.trace ∧
              PollEnv s0.fs.files x evs⌝ ∗
            idKeyPairOutAtPlaced A.repAlloc x.out ans) ∗
            idOwnFutBoxAtPlaced x.fut x.self 1#8 ∗ dirAt A.repAlloc x.self x.own ∗
            lsLogOff ∗ A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp stk }

def idRegIdPollSpecPlaced [LibsignalPlacement] {M : AllocCostModel} (rd : ReadRule)
    (pathOk : List (BitVec 8) → Prop) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (PollEnv : FsFiles → IdOwnPollGhostPlaced → List AllocEvent → Prop)
    (stk : Nat) : Spec (IdOwnPollGhostPlaced × M.σ) :=
  CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
    { pre := fun (x, st) s =>
        ⌜s.readReg64 .x0 = x.fut ∧ s.readReg64 .x8 = x.out ∧
          x.own.path.length < 2 ^ 32 ∧
          pathOk (pathOf x.own.path (CryptoVerification.SignalSession.Cli.utf8 "registration-id")) ∧
          FitsEnv M lim st (PollEnv s.fs.files x)⌝ ∗
          idOwnFutBoxAtPlaced x.fut x.self 0#8 ∗ dirAt A.repAlloc x.self x.own ∗
          memRegion x.out 48 ∗ A.pool lim st s ∗ stackAt s.sp stk
      post := fun (x, st) s0 sf =>
        ∃∗ evs : List AllocEvent,
          (∃∗ ans : Except Unit (BitVec 32),
            ⌜ans = (CryptoVerification.SignalSession.Cli.IdGhost.mk x.own (.new [])).regId rd s0.fs.files ∧ sf.trace = s0.trace ∧
              PollEnv s0.fs.files x evs⌝ ∗
            idRegIdOutAtPlaced A.repAlloc x.out ans) ∗
            idOwnFutBoxAtPlaced x.fut x.self 1#8 ∗ dirAt A.repAlloc x.self x.own ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp stk }

/-! ## 7. Relocatable `Main` allocator, callee, I/O, and `run` contracts -/

/-- Budget-threaded 14-field allocator and `libc` memory contract bundle on `lsProg_617 H` (`VmPreserved` on non-allocating hooks). -/
structure AllocContractsXCliPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop where
  alloc : subroutine_ok (lsProg_617 H) (lsρ lsRustAllocSymCli)
    (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (rustAllocSpecWithStack M A lim false extHookStack))
  dealloc : subroutine_ok (lsProg_617 H) (lsρ lsRustDeallocSymCli)
    (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (rustDeallocExternSpecWithStack M A lim extHookStack))
  realloc : subroutine_ok (lsProg_617 H) (lsρ lsRustReallocSymCli)
    (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (rustReallocExternSpecWithStack M A lim extHookStack))
  shim : ∀ (stk : Nat), extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    subroutine_ok (lsProg_617 H) (lsρ lsRustNoAllocShimSymCli)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (withStack sessionShimBudgetSpec stk))
  memcpy : ∀ (stk : Nat), extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    subroutine_ok (lsProg_617 H) (lsρ memcpyName)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (withVmPreserved (libcMemcpySpec stk)))
  session_memcpy : ∀ (stk : Nat), extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    subroutine_ok (lsProg_617 H) (lsρ memcpyName)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (sessionMemcpyBudgetSpec stk))
  memcpy_region : ∀ (stk : Nat), extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    subroutine_ok (lsProg_617 H) (lsρ memcpyName)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (withStack (withVmPreserved memcpyRegionSpec) stk))
  session_memcpy_region : ∀ (stk : Nat), extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    subroutine_ok (lsProg_617 H) (lsρ memcpyName)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (withStack sessionMemcpyRegionBudgetSpec stk))
  memmove : ∀ (stk : Nat), extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    subroutine_ok (lsProg_617 H) (lsρ memmoveName)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (withVmPreserved (libcMemmoveSpec stk)))
  session_memmove : ∀ (stk : Nat), extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    subroutine_ok (lsProg_617 H) (lsρ memmoveName)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (sessionMemmoveBudgetSpec stk))
  memset : ∀ (stk : Nat), extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    subroutine_ok (lsProg_617 H) (lsρ memsetName)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (withVmPreserved (libcMemsetSpec stk)))
  session_memset : ∀ (stk : Nat), extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    subroutine_ok (lsProg_617 H) (lsρ memsetName)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (sessionMemsetBudgetSpec stk))
  memset_region : ∀ (stk : Nat), extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    subroutine_ok (lsProg_617 H) (lsρ memsetName)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (withStack (withVmPreserved memsetRegionSpec) stk))
  session_memset_region : ∀ (stk : Nat), extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    subroutine_ok (lsProg_617 H) (lsρ memsetName)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (withStack sessionMemsetRegionBudgetSpec stk))

/-- Budget-threaded 15-field `.keepsFs` allocator and `libc` memory contract bundle on `lsProg_617 H`. -/
structure AllocContractsFsPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop where
  alloc : subroutine_ok (lsProg_617 H) (lsρ lsRustAllocSymCli)
    (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (rustAllocSpecWithStack M A lim false extHookStack).keepsFs)
  dealloc : subroutine_ok (lsProg_617 H) (lsρ lsRustDeallocSymCli)
    (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (rustDeallocExternSpecWithStack M A lim extHookStack).keepsFs)
  realloc : subroutine_ok (lsProg_617 H) (lsρ lsRustReallocSymCli)
    (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (rustReallocExternSpecWithStack M A lim extHookStack).keepsFs)
  shim : ∀ (stk : Nat), extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    subroutine_ok (lsProg_617 H) (lsρ lsRustNoAllocShimSymCli)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (withStack sessionShimBudgetSpec stk).keepsFs)
  memcpy : ∀ (stk : Nat), extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    subroutine_ok (lsProg_617 H) (lsρ memcpyName)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (withVmPreserved (libcMemcpySpec stk)).keepsFs)
  session_memcpy : ∀ (stk : Nat), extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    subroutine_ok (lsProg_617 H) (lsρ memcpyName)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (sessionMemcpyBudgetSpec stk).keepsFs)
  memcpy_region : ∀ (stk : Nat), extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    subroutine_ok (lsProg_617 H) (lsρ memcpyName)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (withStack (withVmPreserved memcpyRegionSpec) stk).keepsFs)
  session_memcpy_region : ∀ (stk : Nat), extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    subroutine_ok (lsProg_617 H) (lsρ memcpyName)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (withStack sessionMemcpyRegionBudgetSpec stk).keepsFs)
  memmove : ∀ (stk : Nat), extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    subroutine_ok (lsProg_617 H) (lsρ memmoveName)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (withVmPreserved (libcMemmoveSpec stk)).keepsFs)
  session_memmove : ∀ (stk : Nat), extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    subroutine_ok (lsProg_617 H) (lsρ memmoveName)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (sessionMemmoveBudgetSpec stk).keepsFs)
  memset : ∀ (stk : Nat), extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    subroutine_ok (lsProg_617 H) (lsρ memsetName)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (withVmPreserved (libcMemsetSpec stk)).keepsFs)
  session_memset : ∀ (stk : Nat), extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    subroutine_ok (lsProg_617 H) (lsρ memsetName)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (sessionMemsetBudgetSpec stk).keepsFs)
  memset_region : ∀ (stk : Nat), extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    subroutine_ok (lsProg_617 H) (lsρ memsetName)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (withStack (withVmPreserved memsetRegionSpec) stk).keepsFs)
  session_memset_region : ∀ (stk : Nat), extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    subroutine_ok (lsProg_617 H) (lsρ memsetName)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (withStack sessionMemsetRegionBudgetSpec stk).keepsFs)
  session_memcpy_region_ro : ∀ (stk : Nat), extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    subroutine_ok (lsProg_617 H) (lsρ memcpyName)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (withStack (withVmPreserved sessionMemcpyRegionROSpec) stk).keepsFs)

structure MainCalleesPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks)
    (uuidParse : UuidParser) (hookStack resStack : Nat) : Prop where
  alloc : SpecsPlacedBudget.AllocContractsXCliPlaced A lim H
  allocFs : SpecsPlacedBudget.AllocContractsFsPlaced A lim H
  strlen : subroutine_ok (lsProg_617 H) (lsρ "strlen")
    (withLsRoCl lsmpl (withVmPreserved (strlenSpec hookStack)))
  fromUtf8 : subroutine_ok (lsProg_617 H) (lsρ lsFromUtf8Sym)
    (withLsRoCl lsmpl (withVmPreserved (fromUtf8AsciiSpec hookStack)))
  address : subroutine_ok (lsProg_617 H) (lsmpl.base 580)
    (withLsRoCl lsmpl (addressSpec A lim uuidParse resStack))
  reserve16 : subroutine_ok (lsProg_617 H) (lsmpl.base 588)
    (withLsRoCl lsmpl (reserve16Spec A lim resStack))
  reserve1 : subroutine_ok (lsProg_617 H) (lsmpl.base 588)
    (withLsRoCl lsmpl (doReserveSpecOf resStack A lim).keepsFs)
  tryAllocateIn3 : subroutine_ok (lsProg_617 H) (lsmpl.base 561)
    (withLsRoCl lsmpl (tryAllocateInSpecOf resStack A lim).keepsFs)

open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)

def readStdinSpecPlaced [LibsignalPlacement] {M : AllocCostModel} (io : IoModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat) :
    Spec (ReadStdinGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x8 = x.ret ∧ io.stdin s.fs = some x.bs ∧
      FitsEnv M lim st (ReadStdinEnv x.bs) ∧ LsRetAddr624 (s.readReg64 .lr)⌝ ∗
      memRegion x.ret 24 ∗ stackAt s.sp stk ∗ A.pool lim st s
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜ReadStdinEnv x.bs evs⌝ ∗
        (∃∗ r : Except Unit (List (BitVec 8)),
          ⌜sf.fs.files = s0.fs.files ∧ r = CryptoVerification.SignalSession.readStdinResult x.bs ∧ sf.trace = s0.trace⌝ ∗
            ioVecAt A.repAlloc x.ret r) ∗
        stackAt s0.sp stk ∗ A.pool lim (M.stepEvents evs st) sf

def readFileLitSpecPlaced {M : AllocCostModel} (io : IoModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (stk : Nat)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop := ReadFileRuleEnv io.rd) :
    Spec (ReadFileLitGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.pathA ∧ (s.readReg64 .x1).toNat = x.path.length ∧
      s.readReg64 .x8 = x.ret ∧ x.path.length < 2 ^ 32 ∧ io.pathOk x.path ∧
      FitsEnv M lim st (ReadEnv s.fs.files x.path)⌝ ∗
      (x.pathA ↦ᵣ x.path) ∗ memRegion x.ret 24 ∗ stackAt s.sp stk ∗ A.pool lim st s
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜ReadEnv s0.fs.files x.path evs⌝ ∗
        (∃∗ r : Except Unit (List (BitVec 8)),
          ⌜sf.fs.files = s0.fs.files ∧ r = io.rd s0.fs.files x.path ∧ sf.trace = s0.trace⌝ ∗
            ioVecAt A.repAlloc x.ret r) ∗
        (x.pathA ↦ᵣ x.path) ∗ stackAt s0.sp stk ∗ A.pool lim (M.stepEvents evs st) sf

def writeFileSpecPlaced {M : AllocCostModel} (io : IoModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (stk : Nat) : Spec (WriteFileGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.pathA ∧ (s.readReg64 .x1).toNat = x.path.length ∧
      s.readReg64 .x2 = x.buf ∧ (s.readReg64 .x3).toNat = x.bs.length ∧
      x.path.length < 2 ^ 32 ∧ io.pathOk x.path ∧
      FitsEnv M lim st (WriteFileEnv x.path.length)⌝ ∗
      (x.pathA ↦ₛ x.path) ∗ (x.buf ↦ₛ x.bs) ∗ stackAt s.sp stk ∗ A.pool lim st s
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜WriteFileEnv x.path.length evs ∧
        (match io.wr s0.fs.files x.path x.bs with
         | some F' => sf.readReg64 .x0 = 0#64 ∧ sf.fs.files = F'
         | none => sf.readReg64 .x0 = 1#64 ∧ sf.fs.files = s0.fs.files) ∧
        s0.trace <+: sf.trace ∧
        ProcessOutcome.traceStreamBytes .stdout sf.trace =
          ProcessOutcome.traceStreamBytes .stdout s0.trace⌝ ∗
        (x.pathA ↦ₛ x.path) ∗ (x.buf ↦ₛ x.bs) ∗ stackAt s0.sp stk ∗
        A.pool lim (M.stepEvents evs st) sf

def writeStdoutSpecPlaced {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (stk : Nat) : Spec (WriteStdoutGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.buf ∧ (s.readReg64 .x1).toNat = x.bs.length ∧
      FitsEnv M lim st WriteStdoutEnv⌝ ∗
      (x.buf ↦ₛ x.bs) ∗ stackAt s.sp stk ∗ A.pool lim st s
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜WriteStdoutEnv evs ∧
        sf.readReg64 .x0 = 0#64 ∧ sf.fs.files = s0.fs.files ∧ s0.trace <+: sf.trace ∧
        ProcessOutcome.traceStreamBytes .stdout sf.trace =
          ProcessOutcome.traceStreamBytes .stdout s0.trace ++ x.bs⌝ ∗
        (x.buf ↦ₛ x.bs) ∗ stackAt s0.sp stk ∗ A.pool lim (M.stepEvents evs st) sf

structure MainIoPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks)
    (io : IoModel) (hookStack : Nat) : Prop where
  readStdin : subroutine_ok (lsProg_617 H) (lsρ lsReadStdinSym)
    (withLsRoCl lsmpl (readStdinSpecPlaced io A lim hookStack))
  readFile : subroutine_ok (lsProg_617 H) (lsρ lsReadFileSym)
    (withLsRoCl lsmpl (readFileLitSpecPlaced io A lim hookStack))
  writeFile : subroutine_ok (lsProg_617 H) (lsρ lsWriteFileSym)
    (withLsRoCl lsmpl (writeFileSpecPlaced io A lim hookStack))
  writeStdout : subroutine_ok (lsProg_617 H) (lsρ lsWriteStdoutSym)
    (withLsRoCl lsmpl (writeStdoutSpecPlaced A lim hookStack))

/-- Budget-threaded `signal_session::run` (Block `579`) specification parameterized by `RunEnv : RunCall → List AllocEvent → Prop`. -/
def runSpecPlaced [LibsignalPlacement] {M : AllocCostModel} (CodeOk : Memory → Prop)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (RunEnv : RunCall → List AllocEvent → Prop)
    (uuidParse : UuidParser) (Run : Inputs → RunAnswer → Prop)
    (wrOk : List (BitVec 8) → Prop) (resStack : Nat) : Spec (RunCall × M.σ) where
  pre := fun (g, st) s0 =>
    ⌜CodeOk s0.mem ∧ Run g.i g.a ∧ parseArgs uuidParse (g.i.argv.map bytesOfString) = some g.c ∧
      s0.readReg64 .x0 = g.res ∧ s0.readReg64 .x1 = g.call ∧ s0.readReg64 .x2 = g.stores ∧
      s0.readReg64 .x3 = g.inp ∧
      s0.readReg64 .x4 = BitVec.ofNat 64 (inputOf g.i g.c).length ∧
      s0.fs.files = (initFsState (cliInputs g.i)).files ∧
      ProcessOutcome.traceStreamBytes .stdout s0.trace = [] ∧ resStack ≤ s0.sp.toNat ∧
      FitsEnv M lim st (RunEnv g) ∧ LsRetAddr624 (s0.readReg64 .x30)⌝ ∗
      memRegion g.res runResSize ∗ callAt A.repAlloc g.call g.c ∗
      storesAt A.repAlloc g.stores CryptoVerification.SignalSession.Cli.StoresGhost.opened ∗
      (g.inp ↦ₛ inputOf g.i g.c) ∗ coinsInstalledPlaced g.coins (coinsOf g.i) ∗
      tokenInitPlacedAt ∗ lsLogOff ∗ A.pool lim st s0 ∗ stackAt s0.sp resStack
  post := fun (g, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜RunEnv g evs ∧ s0.trace <+: sf.trace ∧
        sf.fs.files = s0.fs.files ∧
        ProcessOutcome.traceStreamBytes .stdout sf.trace =
          ProcessOutcome.traceStreamBytes .stdout s0.trace⌝ ∗
        memRegion g.call 56 ∗ memRegion g.stores 320 ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp resStack ∗
        (∃∗ a' : RunAnswer, ⌜a' ≠ none ∧ a' = g.a⌝ ∗
          runResAt A.repAlloc wrOk g.res a') ∗ anyHeap
  onPanic := fun (g, _) s0 sf => ⌜g.a = none ∨ allocFailedIn s0 sf⌝ ∗ anyHeap

/-- Envelope-erased `signal_session::run` specification with existential post-`run` cost-model state `st' : M.σ`. -/
def runSpecAnyPlaced [LibsignalPlacement] {M : AllocCostModel} (CodeOk : Memory → Prop)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (uuidParse : UuidParser) (Run : Inputs → RunAnswer → Prop)
    (wrOk : List (BitVec 8) → Prop) (resStack : Nat) : Spec (RunCall × M.σ) where
  pre := fun (g, st) s0 =>
    ⌜CodeOk s0.mem ∧ Run g.i g.a ∧ parseArgs uuidParse (g.i.argv.map bytesOfString) = some g.c ∧
      s0.readReg64 .x0 = g.res ∧ s0.readReg64 .x1 = g.call ∧ s0.readReg64 .x2 = g.stores ∧
      s0.readReg64 .x3 = g.inp ∧
      s0.readReg64 .x4 = BitVec.ofNat 64 (inputOf g.i g.c).length ∧
      s0.fs.files = (initFsState (cliInputs g.i)).files ∧
      ProcessOutcome.traceStreamBytes .stdout s0.trace = [] ∧ resStack ≤ s0.sp.toNat ∧
      LsRetAddr624 (s0.readReg64 .x30)⌝ ∗
      memRegion g.res runResSize ∗ callAt A.repAlloc g.call g.c ∗
      storesAt A.repAlloc g.stores CryptoVerification.SignalSession.Cli.StoresGhost.opened ∗
      (g.inp ↦ₛ inputOf g.i g.c) ∗ coinsInstalledPlaced g.coins (coinsOf g.i) ∗
      tokenInitPlacedAt ∗ lsLogOff ∗ A.pool lim st s0 ∗ stackAt s0.sp resStack
  post := fun (g, _) s0 sf =>
    ∃∗ st' : M.σ,
      ⌜s0.trace <+: sf.trace ∧
        sf.fs.files = s0.fs.files ∧
        ProcessOutcome.traceStreamBytes .stdout sf.trace =
          ProcessOutcome.traceStreamBytes .stdout s0.trace⌝ ∗
        memRegion g.call 56 ∗ memRegion g.stores 320 ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        A.pool lim st' sf ∗ stackAt s0.sp resStack ∗
        (∃∗ a' : RunAnswer, ⌜a' ≠ none ∧ a' = g.a⌝ ∗
          runResAt A.repAlloc wrOk g.res a') ∗ anyHeap
  onPanic := fun (g, _) s0 sf => ⌜g.a = none ∨ allocFailedIn s0 sf⌝ ∗ anyHeap

end LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
