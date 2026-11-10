/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Pub.DropSpe.Proof
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Concat2
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropPreKeyMsg
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropSignalMessage
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropStores
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromBase
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address.Pure
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.WritePaths
public import LibsignalBinary.Proofs.SignalSession.Cli.Specs
import LibsignalBinary.Proofs.RecordCodecs.IdentityKeyDecode
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AddressA1
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFs
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Reserve11
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.StrlenUtf8A1
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.TryAllocateIn3
import LibsignalBinary.Proofs.SignalSession.Cli.Pub.BundleRead
import LibsignalBinary.Proofs.SignalSession.Cli.Pub.SplitId
import LibsignalBinary.Proofs.SignalSession.Cli.Pub.SplitSigned
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Glue.BcmpHook
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Glue.FsTraced
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.SigTryFrom
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSat

/-!
# `signal_session::run`: Callee Slots, Hook Bundles, and Stack Budgets

Defines the callee slot abstraction (`CalleeSlot`, `RunSlots`), extern hook bundles (`RunHooks` and
contract-backed `RunHooksExt`), callee contract bundle (`RunCallees`), stack frame budget
(`runFrame = 0x2a50`, `runCalleeNeed`, `runNeed`), and derived leaf and drop callee lemmas for
`signal_session::run`.
-/

@[expose] public section

set_option warningAsError false

namespace CryptoVerification.SignalSession.Cli.RunSkeleton

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open Arm64.Process
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops

/-! ## 1. Re-exported drop and slice-concatenation specs -/

export CryptoVerification.SignalSession.Cli.DropSpeProof (dropSpeSpecStk)
export CryptoVerification.SignalSession.Cli.RunProofs (cliConcatName cliConcat2Spec)
export CryptoVerification.SignalSession.Cli.RunProofs
  (cliDropStoresName DropStoresGhost dropStoresSpec)
export CryptoVerification.SignalSession.Cli.RunProofs
  (cliDropSignalMessageName DropSignalMessageGhost dropSignalMessageSpec)
export CryptoVerification.SignalSession.Cli.RunProofs
  (cliDropPreKeyMsgName DropPreKeyMsgGhost dropPreKeyMsgSpec)

/-! ## 2. Wrapper callee slots -/

abbrev wrapEncryptName : String := "libsignal_cli_ratchet::encrypt"
abbrev wrapDecryptSignalName : String := "libsignal_cli_ratchet::decrypt_signal"
abbrev wrapInitiateName : String := "libsignal_cli_handshake::initiate"
abbrev wrapDecryptPrekeyName : String := "libsignal_cli_handshake::decrypt_prekey"
abbrev kemDeserializeName : String :=
  "<libsignal_protocol::kem::Key<libsignal_protocol::kem::Public>>::deserialize"

/-- Abstract callee contract packaging a ghost parameter type, stack-indexed `Spec`, and minimum stack requirement `need`. -/
structure CalleeSlot where
  Ghost : Type
  spec : Nat → Spec Ghost
  need : Nat

/-- `σ`'s specification holds at `name` for every stack budget `σ.need ≤ stk ≤ 2^63`. -/
def CalleeSlot.Ok (img : Obj.Image) (ext : String → Option (State → State)) (name : String)
    (σ : CalleeSlot) : Prop :=
  ∀ stk, σ.need ≤ stk → stk ≤ 2 ^ 63 →
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name) (σ.spec stk)

/-- Callee slots of `signal_session::run`: `encrypt`, `decryptSignal`, `initiate`, `decryptPrekey`, and `kemDeserialize`. -/
structure RunSlots where
  encrypt : CalleeSlot
  decryptSignal : CalleeSlot
  initiate : CalleeSlot
  decryptPrekey : CalleeSlot
  kemDeserialize : CalleeSlot

/-! ## 3. Hook and callee hypotheses -/

/-- Extern hook hypotheses for `signal_session::run` (instantiated at `cliExterns W` and `A0` by `RunHooks.cli`). -/
structure RunHooks (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State)) :
    Prop where
  alloc : AllocContractsX img A ext
  allocFs : AllocContractsFs img A ext
  memcpyRO : HookSat ext memcpyName SpqrV1.Alloc.sessionMemcpyRegionROSpec
  bcmp : HookSat ext cliBcmpName cliBcmpSpec
  fs : TraceFsSound (tripleRatchetProgAtExt img.base ext)
  utf8 : ∃ err, ext "core::str::converts::from_utf8" = some (fromUtf8Hook err)
  memrchr : ext "core::slice::memchr::memrchr" = some memrchrHook
  allocHooks : AllocHooks A ext
  allocZeroed : HookSat ext allocZeroedName (rustAllocZeroedSpec A)
  allocContracts : AllocContracts img.base A ext
  formatInner : HookSat ext LibsignalTripleRatchet.formatInnerName (LibsignalTripleRatchet.formatInnerSpec A)

/-- Configurable leaf stack budget for `signal_session_io::read_file`. -/
structure RunBudgets where
  readFile : Nat

/-- Direct callee contracts required by `signal_session::run` alongside `RunHooks`. -/
structure RunCallees (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State))
    (B : RunBudgets) (σ : RunSlots) : Prop where
  readFile : subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr Cli.readFileName)
    (readFileSpec cliIo.rd cliWrOk A img B.readFile)
  -- `PreKeySignalMessage::try_from` (`pksmSlotSpec`) is passed separately to `Compose.run_ok'`.
  encrypt : σ.encrypt.Ok img ext wrapEncryptName
  decryptSignal : σ.decryptSignal.Ok img ext wrapDecryptSignalName
  initiate : σ.initiate.Ok img ext wrapInitiateName
  decryptPrekey : σ.decryptPrekey.Ok img ext wrapDecryptPrekeyName
  kemDeserialize : σ.kemDeserialize.Ok img ext kemDeserializeName

/-! ## 4. Derived leaf and drop callees -/

abbrev pathNeed : Nat := 0x70 + max doReserveStackX extHookStack
abbrev splitIdNeed : Nat := 0x60 + dropSpeStackX
abbrev splitSignedNeed : Nat := 0x60 + max splitIdNeed dropSpeStackX
abbrev RunBudgets.dirGetNeed (B : RunBudgets) : Nat :=
  0x70 + max (max pathNeed B.readFile) extHookStack
abbrev RunBudgets.bundleReadNeed (B : RunBudgets) : Nat :=
  0x50 + max (max pathNeed B.readFile) extHookStack

theorem base_aligned {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img) :
    (img.base &&& 0xfff#64) = 0#64 :=
  ProofLib.ObjectLoad.base_aligned_of_loads himg

theorem fromUtf8_ok {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hh : RunHooks img A ext) (hookStack : Nat) :
    subroutine_ok (mProg img ext)
      ((mProg img ext).fnAddr "core::str::converts::from_utf8")
      ((fromUtf8AsciiSpec hookStack).inImage img) :=
  let ⟨_, hext⟩ := hh.utf8
  fromUtf8Ascii_ok hext

theorem runAddress_ok {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hh : RunHooks img A ext) (resStack : Nat)
    (hres : 0xB0 + extHookStack ≤ resStack) (hres64 : resStack ≤ 2 ^ 63) :
    subroutine_ok (mProg img ext) ((mProg img ext).fnAddr addressName)
      ((addressSpec A uuidTryParse resStack).inImage img) :=
  address_ok_a1 hh.allocFs hh.memrchr hres hres64

theorem runTryAllocateIn3_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hh : RunHooks img A ext) (resStack : Nat)
    (hres : finishGrowStackX ≤ resStack) (hres64 : resStack ≤ 2 ^ 63) :
    subroutine_ok (mProg img ext) ((mProg img ext).fnAddr tryAllocateIn3Name)
      ((tryAllocateInSpecOf resStack A).keepsFs.inImage img) :=
  tryAllocateIn3_okFs hh.allocFs hres hres64

theorem reserve_ok {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hh : RunHooks img A ext) {resStack : Nat} (hstk : doReserveStackX ≤ resStack) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr cliDoReserveName)
      ((SpqrV1.Varint.doReserveSpecOf resStack A).inImage img) :=
  cliDoReserve_ok hh.alloc hstk

theorem dropStores_ok {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hh : RunHooks img A ext) (stk : Nat)
    (hstk : 96 + extHookStack ≤ stk) (hstk64 : stk ≤ 2 ^ 64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr cliDropStoresName)
      ((dropStoresSpec A stk).inImage img) :=
  CryptoVerification.SignalSession.Cli.RunProofs.cliDropStores_ok hh.alloc stk hstk hstk64

theorem dropSignalMessage_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hh : RunHooks img A ext) (stk : Nat)
    (hstk : 32 + extHookStack ≤ stk) (hstk64 : stk ≤ 2 ^ 64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr cliDropSignalMessageName)
      ((dropSignalMessageSpec A stk).inImage img) :=
  CryptoVerification.SignalSession.Cli.RunProofs.cliDropSignalMessage_ok hh.alloc stk hstk hstk64

theorem dropPreKeyMsg_ok {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hh : RunHooks img A ext) (stk : Nat)
    (hstk : 32 + extHookStack ≤ stk) (hstk64 : stk ≤ 2 ^ 64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr cliDropPreKeyMsgName)
      ((dropPreKeyMsgSpec A stk).inImage img) :=
  CryptoVerification.SignalSession.Cli.RunProofs.cliDropPreKeyMsg_ok hh.alloc stk hstk hstk64

theorem sigTryFrom_ok {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) (hh : RunHooks img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr tryFromName) (tryFromSpec A img) :=
  CryptoVerification.SignalSession.Cli.RunProofs.cliSigTryFrom_ok
    ⟨fun s _ => s, fun _ b => b, fun _ b => b, fun a _ => a, fun a => a⟩ himg hh.alloc

theorem dropSpeX_ok {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) (hh : RunHooks img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr cliDropSpeName)
      ((dropSpeSpecX A).inImage img) :=
  CryptoVerification.SignalSession.Cli.DropSpeProof.cliDropSpe_ok_x_proof himg hh.alloc

theorem dropSpe_ok {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) (hh : RunHooks img A ext) (stk : Nat)
    (hstk : 32 + extHookStack ≤ stk) (hstk64 : stk ≤ 2 ^ 64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr cliDropSpeName)
      ((dropSpeSpecStk A stk).inImage img) :=
  CryptoVerification.SignalSession.Cli.DropSpeProof.cliDropSpe_ok_stk himg hh.alloc stk hstk hstk64

theorem concat_ok {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hh : RunHooks img A ext) (stk : Nat)
    (hstk : 96 + extHookStack ≤ stk) (hstk64 : stk ≤ 2 ^ 64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr cliConcatName)
      ((cliConcat2Spec A stk).inImage img) :=
  CryptoVerification.SignalSession.Cli.RunProofs.cliConcat2_ok hh.alloc hh.memcpyRO stk hstk hstk64

theorem path_ok {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooks img A ext) {stk : Nat}
    (hstk : pathNeed ≤ stk) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr pathName) (pathSpec A img stk) :=
  Path.path_ok_of_deps hh.alloc hh.memcpyRO (reserve_ok hh (Nat.le_refl _)) hstk (base_aligned himg)

theorem splitId_ok {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) (hh : RunHooks img A ext) {stk : Nat}
    (hstk : splitIdNeed ≤ stk) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr splitIdName) (splitIdSpec A img stk) :=
  SplitId.splitId_ok_of_deps himg hh.alloc (dropSpeX_ok himg hh) hstk (base_aligned himg)

theorem splitSigned_ok {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) (hh : RunHooks img A ext) {stk : Nat}
    (hstk : splitSignedNeed ≤ stk) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr splitSignedName) (splitSignedSpec A img stk) :=
  SplitSigned.splitSigned_ok_of_deps himg hh.alloc (splitId_ok himg hh (Nat.le_refl _))
    (dropSpeX_ok himg hh) hstk (base_aligned himg)

theorem dirGet_ok {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    {B : RunBudgets} {σ : RunSlots} (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooks img A ext) (hc : RunCallees img A ext B σ) {stk : Nat}
    (hstk : B.dirGetNeed ≤ stk) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dirGetName)
      (dirGetSpec cliIo.rd cliWrOk A img stk) :=
  Get.dirGet_ok_of_deps himg (fun _ h => h.2) hh.alloc hh.memcpyRO hh.bcmp (path_ok himg hh (Nat.le_refl _))
    hc.readFile hh.fs hstk (base_aligned himg)

theorem bundleRead_ok {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    {B : RunBudgets} {σ : RunSlots} (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooks img A ext) (hc : RunCallees img A ext B σ) {stk : Nat}
    (hstk : B.bundleReadNeed ≤ stk) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr bundleReadName)
      (bundleReadSpec cliIo.rd cliWrOk A img stk) :=
  BundleRead.bundleRead_ok_of_deps himg (fun _ h => h.2) hh.alloc (path_ok himg hh (Nat.le_refl _))
    hc.readFile hh.fs hstk (base_aligned himg)

theorem identityKeyDecode_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (himg : Obj.Loads libsignalSessionImage img) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr
        CryptoVerification.RecordCodecsBinary.identityKeyDecodeName)
      (CryptoVerification.RecordCodecsBinary.identityKeyDecodeSpec A img) :=
  CryptoVerification.RecordCodecsBinary.IdentityKeyDecode.identityKeyDecode_ok_of_pkTryFrom
    (CryptoVerification.LibsignalTripleRatchet.pkTryFrom_ok_ext img ext himg) (base_aligned himg)

/-- `PublicKey::deserialize` contract on valid keys (`PublicKey.deserialize bs = .ok pk`). -/
theorem pkDeserialize_ok (img : Obj.Image) (ext : String → Option (State → State)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr "<libsignal_core::curve::PublicKey>::deserialize")
      (CryptoVerification.LibsignalSession.FindReceiverChainIndex.deserializeSpec img.base) :=
  CryptoVerification.LibsignalSession.FindReceiverChainIndex.deserialize_ok img.base
    (Rust.withPanics ext)

/-- Full `PublicKey::deserialize` contract covering both valid keys and decode errors. -/
theorem pkDeserializeFull_ok (img : Obj.Image) (ext : String → Option (State → State)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr "<libsignal_core::curve::PublicKey>::deserialize")
      ((CryptoVerification.LibsignalTripleRatchet.Wire.deserializeFullSpec img.base).inImage img) :=
  CryptoVerification.LibsignalTripleRatchet.subroutine_ok_inImage_of_subroutine_ok img
    (CryptoVerification.LibsignalTripleRatchet.Wire.deserializeFull_ok img.base (Rust.withPanics ext))

/-- Instantiates `RunHooks` unconditionally at `cliExterns W` and `E2E.HooksE.A0`. -/
theorem RunHooks.cli (W : CliHooks) (img : Obj.Image) :
    RunHooks img E2E.HooksE.A0 (cliExterns W) where
  alloc := allocContractsX_cli W img
  allocFs := allocContractsFs_cli W img
  memcpyRO := cli_hookSat_memcpy_region_ro W
  bcmp := RunGlue.cli_hookSat_bcmp W
  fs := RunGlue.traceFsSound_cli W img.base
  utf8 := ⟨W.utf8Err, cliExterns_row W (List.mem_append_right _ (by simp))⟩
  memrchr := cliExterns_memrchr W
  allocHooks := Slots.cliExterns_allocHooks W
  allocZeroed := Slots.cliExterns_allocZeroed W
  allocContracts := Slots.allocContracts_cli W img
  formatInner := Slots.cliExterns_formatInner W

/-! ## 5. Stack frame and callee budgets -/

/-- Stack frame size (`0x2a50` bytes, including saved registers) of `signal_session::run`. -/
abbrev runFrame : Nat := 0x2a50

/-- Maximum stack budget required among all direct callees and extern hooks of `signal_session::run`. -/
def runCalleeNeed (B : RunBudgets) (σ : RunSlots) : Nat :=
  [ 0xB0 + extHookStack,             -- address
    finishGrowStackX,                 -- try_allocate_in [local#3]
    B.readFile,                       -- read_file
    pathNeed, B.dirGetNeed, B.bundleReadNeed, splitIdNeed, splitSignedNeed,
    0x60,                             -- IdentityKey::decode
    smallRootStack,                   -- SignalMessage::try_from
    CryptoVerification.E2E.Pqxdh.ResponderWire.preKeyTryFromStack,
    32 + extHookStack,                -- drop_glue<SPE> [local#4], <SignalMessage>, <PKSM>
    96 + extHookStack,                -- drop_glue<Stores>, concat [local#3]
    extHookStack,                     -- direct hook calls
    σ.encrypt.need, σ.decryptSignal.need, σ.initiate.need, σ.decryptPrekey.need,
    σ.kemDeserialize.need ].foldr max 0

/-- Total stack requirement `runFrame + runCalleeNeed B σ` of `signal_session::run`. -/
def runNeed (B : RunBudgets) (σ : RunSlots) : Nat := runFrame + runCalleeNeed B σ

/-! ## 6. Contract-backed `RunHooksExt` and callees -/

/-- Contract-backed counterpart of `RunHooks`, replacing concrete `fromUtf8Hook` and `memrchrHook`
equalities and zero-stack `AllocContracts` with `HookSat` contracts. -/
structure RunHooksExt (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop where
  alloc : AllocContractsX img A ext
  allocFs : AllocContractsFs img A ext
  memcpyRO : HookSat ext memcpyName
    (SpqrV1.Alloc.sessionMemcpyRegionROSpecWithStack CliExt.memHookStack)
  bcmp : HookSat ext cliBcmpName cliBcmpSpec
  fs : TraceFsSound (tripleRatchetProgAtExt img.base ext)
  utf8 : HookSat ext "core::str::converts::from_utf8" CliExt.fromUtf8Spec
  memrchr : HookSat ext "core::slice::memchr::memrchr" CliExt.memrchrSpec
  allocHooks : AllocHooks A ext
  allocZeroed : HookSat ext allocZeroedName (rustAllocZeroedSpec A)
  formatInner : HookSat ext LibsignalTripleRatchet.formatInnerName
    (LibsignalTripleRatchet.formatInnerSpec A)

abbrev extRunBudgets : RunBudgets := { readFile := extHookStack }

private theorem stackAt_split_ge_skel {sp : BitVec 64} {inner stk : Nat}
    (hle : inner ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    stackAt sp stk =
      memRegion (sp - BitVec.ofNat 64 stk) (stk - inner) ∗ stackAt sp inner := by
  have h1 := stackAt_split_bottom sp inner (stk - inner) (by omega)
  rwa [Nat.add_sub_of_le hle] at h1

theorem RunHooksExt.memcpyRO_withStack {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hh : RunHooksExt img A ext)
    (stk : Nat) (hle : CliExt.memHookStack ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    HookSat ext memcpyName (SpqrV1.Alloc.sessionMemcpyRegionROSpecWithStack stk) := by
  obtain ⟨f, hf, hok⟩ := hh.memcpyRO
  refine ⟨f, hf, fun ⟨dst, src, bs⟩ R s0 hrun hpre hsp => ?_⟩
  have hsplit := stackAt_split_ge_skel (sp := s0.sp) hle hmax
  let R' : SepProp := memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - CliExt.memHookStack) ∗ R
  have hpre' : s0.mem ⊨
      (SpqrV1.Alloc.sessionMemcpyRegionROSpecWithStack CliExt.memHookStack).pre
        (dst, src, bs) s0 ∗ R' := by
    dsimp only [SpqrV1.Alloc.sessionMemcpyRegionROSpecWithStack, R'] at hpre ⊢
    rw [hsplit] at hpre
    ac_nf at hpre ⊢
  obtain ⟨hkf, hsym, hout⟩ := hok (dst, src, bs) R' s0 hrun hpre' hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hp⟩ | ⟨_, _, hp⟩ | ⟨_, hp⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [SpqrV1.Alloc.sessionMemcpyRegionROSpecWithStack, R'] at hpost ⊢
    rw [hsplit]
    ac_nf at hpost ⊢
  · dsimp only [SpqrV1.Alloc.sessionMemcpyRegionROSpecWithStack] at hp
    rw [satisfies_pure_sepConj] at hp; exact hp.1.elim
  · dsimp only [SpqrV1.Alloc.sessionMemcpyRegionROSpecWithStack] at hp
    rw [satisfies_pure_sepConj] at hp; exact hp.1.elim
  · dsimp only [SpqrV1.Alloc.sessionMemcpyRegionROSpecWithStack] at hp
    rw [satisfies_pure_sepConj] at hp; exact hp.1.elim

theorem RunHooksExt.memcpyRO_X {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hh : RunHooksExt img A ext) :
    HookSat ext memcpyName SpqrV1.Alloc.sessionMemcpyRegionROSpecX :=
  hh.memcpyRO_withStack extHookStack (by decide) extHookStack_le

theorem RunHooksExt.utf8Ascii {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hh : RunHooksExt img A ext) :
    HookSat ext "core::str::converts::from_utf8" (fromUtf8AsciiSpec extHookStack) := by
  obtain ⟨f, hf, hok⟩ := hh.utf8
  exact ⟨f, hf, hok⟩

theorem RunHooksExt.memrchrMain {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hh : RunHooksExt img A ext) :
    HookSat ext "core::slice::memchr::memrchr" (MainHops.memrchrSpec extHookStack) := by
  obtain ⟨f, hf, hok⟩ := hh.memrchr
  exact ⟨f, hf, fun x R s0 hrun hpre hsp => hok ⟨x.c, x.p, x.bs⟩ R s0 hrun hpre hsp⟩

theorem RunHooks.toExt {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hh : RunHooks img A ext) :
    RunHooksExt img A ext where
  alloc := hh.alloc
  allocFs := hh.allocFs
  memcpyRO := by
    obtain ⟨f, hf, hok⟩ := hh.memcpyRO
    refine ⟨f, hf, fun ⟨dst, src, bs⟩ R s0 hrun hpre hsp => ?_⟩
    have hw := hookOk_withStack hok CliExt.memHookStack
    have hok' := hw (dst, src, bs) R s0 hrun
      (by
        dsimp only [SpqrV1.Alloc.sessionMemcpyRegionROSpecWithStack, withStack,
          SpqrV1.Alloc.sessionMemcpyRegionROSpec] at hpre ⊢
        ac_nf at hpre ⊢) hsp
    obtain ⟨hkf, hsym, hout⟩ := hok'
    refine ⟨hkf, hsym, ?_⟩
    rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hp⟩ | ⟨_, _, hp⟩ | ⟨_, hp⟩
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [SpqrV1.Alloc.sessionMemcpyRegionROSpecWithStack, withStack,
        SpqrV1.Alloc.sessionMemcpyRegionROSpec] at hpost ⊢
      ac_nf at hpost ⊢
    · dsimp only [withStack, SpqrV1.Alloc.sessionMemcpyRegionROSpec] at hp
      rw [satisfies_pure_sepConj] at hp; exact hp.1.elim
    · dsimp only [withStack, SpqrV1.Alloc.sessionMemcpyRegionROSpec] at hp
      rw [satisfies_pure_sepConj] at hp; exact hp.1.elim
    · dsimp only [withStack, SpqrV1.Alloc.sessionMemcpyRegionROSpec] at hp
      rw [satisfies_pure_sepConj] at hp; exact hp.1.elim
  bcmp := hh.bcmp
  fs := hh.fs
  utf8 := by
    obtain ⟨err, hext⟩ := hh.utf8
    exact ⟨fromUtf8Hook err, hext, fromUtf8Hook_ok extHookStack err⟩
  memrchr := ⟨memrchrHook, hh.memrchr, fun x R s0 hrun hpre hsp =>
    memrchrHook_ok extHookStack ⟨x.c, x.p, x.bs⟩ R s0 hrun hpre hsp⟩
  allocHooks := hh.allocHooks
  allocZeroed := hh.allocZeroed
  formatInner := hh.formatInner

/-- Constructs `RunHooksExt` on `cliExternsWith ext` from `CliExternsOk P A ext`. -/
theorem RunHooksExt.of_externsOk {P : E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P A ext) (img : Obj.Image) :
    RunHooksExt img A (cliExternsWith ext) where
  alloc := allocContractsX_of_externsOk img hOk
  allocFs := allocContractsFs_of_externsOk img hOk
  memcpyRO := memcpyRegionRO_of_externsOk hOk
  bcmp := RunGlue.hookSat_bcmp_of_externsOk hOk
  fs := RunGlue.traceFsSound_of_externsOk hOk img.base
  utf8 := RunGlue.hookSat_cliExternsWith
    (by simp [E2E.isImagePanicSymbol, E2E.extraImagePanicNames, Rust.isPanicSymbol])
    hOk.fromUtf8
  memrchr := RunGlue.hookSat_cliExternsWith
    (by simp [E2E.isImagePanicSymbol, E2E.extraImagePanicNames, Rust.isPanicSymbol])
    hOk.memrchr
  allocHooks :=
    { alloc := RunGlue.hookSat_cliExternsWith
        (by simp [E2E.isImagePanicSymbol, E2E.extraImagePanicNames, Rust.isPanicSymbol])
        hOk.alloc.alloc
      dealloc := RunGlue.hookSat_cliExternsWith
        (by simp [E2E.isImagePanicSymbol, E2E.extraImagePanicNames, Rust.isPanicSymbol])
        hOk.alloc.dealloc
      realloc := RunGlue.hookSat_cliExternsWith
        (by simp [E2E.isImagePanicSymbol, E2E.extraImagePanicNames, Rust.isPanicSymbol])
        hOk.alloc.realloc }
  allocZeroed := RunGlue.hookSat_cliExternsWith
    (by simp [E2E.isImagePanicSymbol, E2E.extraImagePanicNames, Rust.isPanicSymbol, allocZeroedName])
    hOk.allocZeroed
  formatInner := RunGlue.hookSat_cliExternsWith
    (by simp [E2E.isImagePanicSymbol, E2E.extraImagePanicNames, Rust.isPanicSymbol,
      LibsignalTripleRatchet.formatInnerName])
    hOk.formatInner

theorem runHooksExt_of_externsOk {P : E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (img : Obj.Image) (hOk : CliExternsOk P A ext) :
    RunHooksExt img A (cliExternsWith ext) :=
  RunHooksExt.of_externsOk hOk img

theorem RunHooksExt.cli (W : CliHooks) (img : Obj.Image) :
    RunHooksExt img E2E.HooksE.A0 (cliExterns W) :=
  (RunHooks.cli W img).toExt

theorem RunHooksExt.fromUtf8_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hh : RunHooksExt img A ext)
    (hookStack : Nat := extHookStack)
    (hle : extHookStack ≤ hookStack := by decide)
    (hmax : hookStack ≤ 2 ^ 64 := by decide) :
    subroutine_ok (mProg img ext)
      ((mProg img ext).fnAddr "core::str::converts::from_utf8")
      ((fromUtf8AsciiSpec hookStack).inImage img) :=
  fromUtf8Ascii_ok_of_hookSat hh.utf8 hle hmax

theorem runFromUtf8_ok_ext {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hh : RunHooksExt img A ext)
    (hookStack : Nat := extHookStack)
    (hle : extHookStack ≤ hookStack := by decide)
    (hmax : hookStack ≤ 2 ^ 64 := by decide) :
    subroutine_ok (mProg img ext)
      ((mProg img ext).fnAddr "core::str::converts::from_utf8")
      ((fromUtf8AsciiSpec hookStack).inImage img) :=
  hh.fromUtf8_ok hookStack hle hmax

theorem runAddress_ok_ext {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hh : RunHooksExt img A ext) (resStack : Nat)
    (hres : 0xB0 + extHookStack ≤ resStack) (hres64 : resStack ≤ 2 ^ 63) :
    subroutine_ok (mProg img ext) ((mProg img ext).fnAddr addressName)
      ((addressSpec A uuidTryParse resStack).inImage img) :=
  address_ok_of_hookSat hh.allocFs hh.memrchr hres hres64

theorem runTryAllocateIn3_ok_ext {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hh : RunHooksExt img A ext) (resStack : Nat)
    (hres : finishGrowStackX ≤ resStack) (hres64 : resStack ≤ 2 ^ 63) :
    subroutine_ok (mProg img ext) ((mProg img ext).fnAddr tryAllocateIn3Name)
      ((tryAllocateInSpecOf resStack A).keepsFs.inImage img) :=
  tryAllocateIn3_okFs hh.allocFs hres hres64

theorem reserve_ok_ext {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hh : RunHooksExt img A ext)
    {resStack : Nat} (hstk : doReserveStackX ≤ resStack) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr cliDoReserveName)
      ((SpqrV1.Varint.doReserveSpecOf resStack A).inImage img) :=
  cliDoReserve_ok hh.alloc hstk

theorem dropStores_ok_ext {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hh : RunHooksExt img A ext) (stk : Nat)
    (hstk : 96 + extHookStack ≤ stk) (hstk64 : stk ≤ 2 ^ 64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr cliDropStoresName)
      ((dropStoresSpec A stk).inImage img) :=
  CryptoVerification.SignalSession.Cli.RunProofs.cliDropStores_ok hh.alloc stk hstk hstk64

theorem dropSignalMessage_ok_ext {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hh : RunHooksExt img A ext) (stk : Nat)
    (hstk : 32 + extHookStack ≤ stk) (hstk64 : stk ≤ 2 ^ 64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr cliDropSignalMessageName)
      ((dropSignalMessageSpec A stk).inImage img) :=
  CryptoVerification.SignalSession.Cli.RunProofs.cliDropSignalMessage_ok hh.alloc stk hstk hstk64

theorem dropPreKeyMsg_ok_ext {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hh : RunHooksExt img A ext) (stk : Nat)
    (hstk : 32 + extHookStack ≤ stk) (hstk64 : stk ≤ 2 ^ 64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr cliDropPreKeyMsgName)
      ((dropPreKeyMsgSpec A stk).inImage img) :=
  CryptoVerification.SignalSession.Cli.RunProofs.cliDropPreKeyMsg_ok hh.alloc stk hstk hstk64

theorem sigTryFrom_ok_ext {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) (hh : RunHooksExt img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr tryFromName) (tryFromSpec A img) :=
  CryptoVerification.SignalSession.Cli.RunProofs.cliSigTryFrom_ok
    ⟨fun s _ => s, fun _ b => b, fun _ b => b, fun a _ => a, fun a => a⟩ himg hh.alloc

theorem dropSpeX_ok_ext {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) (hh : RunHooksExt img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr cliDropSpeName)
      ((dropSpeSpecX A).inImage img) :=
  CryptoVerification.SignalSession.Cli.DropSpeProof.cliDropSpe_ok_x_proof himg hh.alloc

theorem dropSpe_ok_ext {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) (hh : RunHooksExt img A ext) (stk : Nat)
    (hstk : 32 + extHookStack ≤ stk) (hstk64 : stk ≤ 2 ^ 64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr cliDropSpeName)
      ((dropSpeSpecStk A stk).inImage img) :=
  CryptoVerification.SignalSession.Cli.DropSpeProof.cliDropSpe_ok_stk himg hh.alloc stk hstk hstk64

theorem splitId_ok_ext {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) (hh : RunHooksExt img A ext) {stk : Nat}
    (hstk : splitIdNeed ≤ stk) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr splitIdName) (splitIdSpec A img stk) :=
  SplitId.splitId_ok_of_deps himg hh.alloc (dropSpeX_ok_ext himg hh) hstk (base_aligned himg)

theorem splitSigned_ok_ext {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) (hh : RunHooksExt img A ext) {stk : Nat}
    (hstk : splitSignedNeed ≤ stk) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr splitSignedName) (splitSignedSpec A img stk) :=
  SplitSigned.splitSigned_ok_of_deps himg hh.alloc (splitId_ok_ext himg hh (Nat.le_refl _))
    (dropSpeX_ok_ext himg hh) hstk (base_aligned himg)

theorem bundleRead_ok_of_path_ext {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {B : RunBudgets} {σ : RunSlots}
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooksExt img A ext)
    (hpath : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr pathName) (pathSpec A img pathNeed))
    (hc : RunCallees img A ext B σ) {stk : Nat}
    (hstk : B.bundleReadNeed ≤ stk) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr bundleReadName)
      (bundleReadSpec cliIo.rd cliWrOk A img stk) :=
  BundleRead.bundleRead_ok_of_deps himg (fun _ h => h.2) hh.alloc hpath
    hc.readFile hh.fs hstk (base_aligned himg)

/-! ## 7. Function offset checks -/

example : libsignalSessionCode.fnOff wrapEncryptName =
    num% (ls_off% "libsignal_cli_ratchet::encrypt") :=
  ls_lemma% fnOff "libsignal_cli_ratchet::encrypt"
example : libsignalSessionCode.fnOff wrapDecryptSignalName =
    num% (ls_off% "libsignal_cli_ratchet::decrypt_signal") :=
  ls_lemma% fnOff "libsignal_cli_ratchet::decrypt_signal"
example : libsignalSessionCode.fnOff wrapInitiateName =
    num% (ls_off% "libsignal_cli_handshake::initiate") :=
  ls_lemma% fnOff "libsignal_cli_handshake::initiate"
example : libsignalSessionCode.fnOff wrapDecryptPrekeyName =
    num% (ls_off% "libsignal_cli_handshake::decrypt_prekey") :=
  ls_lemma% fnOff "libsignal_cli_handshake::decrypt_prekey"
example : libsignalSessionCode.fnOff kemDeserializeName =
    num% (ls_off% "<libsignal_protocol::kem::Key<libsignal_protocol::kem::Public>>::deserialize") :=
  ls_lemma% fnOff "<libsignal_protocol::kem::Key<libsignal_protocol::kem::Public>>::deserialize"
example : libsignalSessionCode.fnOff cliDropStoresName =
    num% (ls_off% "core::ptr::drop_glue::<libsignal_cli::stores::Stores>") :=
  ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_cli::stores::Stores>"
example : libsignalSessionCode.fnOff cliConcatName =
    num% (ls_off% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#3]") :=
  ls_lemma% fnOff "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#3]"
example : runFrame = 10832 := rfl

end CryptoVerification.SignalSession.Cli.RunSkeleton

