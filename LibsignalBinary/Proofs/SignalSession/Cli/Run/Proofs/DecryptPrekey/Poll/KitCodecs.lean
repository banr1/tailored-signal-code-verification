/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.KyberKitOk
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitE
public import LibsignalBinary.Proofs.PublicApi.StoreKit.SignedPreKeyStoreKitE
public import LibsignalBinary.Proofs.RecordCodecs.PreKeyDeserialize.Defs
public import LibsignalBinary.Proofs.RecordCodecs.SignedDeps
import LibsignalBinary.Proofs.CliC.SpqrV1.Prost.BytesMerge.Proof
import LibsignalBinary.Proofs.CliC.TripleRatchet.Prost.DropDecodeError
import LibsignalBinary.Proofs.RecordCodecs.DecodeKyberPreKey
import LibsignalBinary.Proofs.RecordCodecs.PreKeyDeserialize
import LibsignalBinary.Proofs.RecordCodecs.SignedAssembly
import LibsignalBinary.Proofs.RecordCodecs.SignedPreKeyDecode
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Decimal
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.GrowOneX
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.PreKeyKitOk
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.SignedPort7.BytesMerge7
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.SignedPort7.SkipField7
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.SignedPort7.VarintDrop7
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.SigTryFrom
import LibsignalBinary.Proofs.SignalSession.Cli.Run.ReadFileHook
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSat
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.KitRelDet
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.TrapBridge
import LibsignalBinary.Proofs.SignalSession.Cli.Store.DropSpeWord
import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPoll
import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll
import LibsignalBinary.Proofs.SignalSession.Cli.Store.PkGetPoll
import LibsignalBinary.Proofs.SignalSession.Cli.Store.PkRemovePoll
import LibsignalBinary.Proofs.SignalSession.Cli.Store.PkShims
import LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll
import LibsignalBinary.Proofs.TripleRatchet.Bytes.Drops
import LibsignalBinary.Proofs.TripleRatchet.Bytes.From

/-!
# CLI Record Decoders and Store-Kit Instantiations

Instantiates `SignedHooks`, `SignedPortDeps`, `PreKeyDeserializeHooks`, and `DecodeDeps` on
`trTrapExterns`, `cliExterns`, and `RunHooksExt`, derives `decodeKyberPreKeySpec`,
`decodeSignedPreKeySpec`, and `preKeyDeserializeSpec`, and discharges the CLI signed, Kyber, and
one-time pre-key store-kit bundles.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.Poll

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.KitInst
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.Slots

set_option maxRecDepth 200000

/-! ## 1. Crate-10 `SignedHooks` & `SignedPortDeps` at `trTrapExterns` and `cliExterns` -/

theorem stage2Contracts_trTrap (W : CliHooks) (img : Obj.Image) :
    Stage2Contracts_trap img.base W.C E2E.HooksE.A0 uuidTryParse
      (spqrV1 W.C.F W.Q.K) (trTrapExterns W.C (cliExterns W)) :=
  Stage2Contracts_trap.of_tripleRatchetProgAt_trap img.base W.C E2E.HooksE.A0
    (spqrV1 W.C.F W.Q.K) (cliExterns W)
    (cliExterns_tripleRatchetHooks W (spqrV1 W.C.F W.Q.K))

theorem cliSignedHooks_trTrap (W : CliHooks) (img : Obj.Image) :
    SignedHooks img.base E2E.HooksE.A0 (trTrapExterns W.C (cliExterns W)) where
  alloc := (stage2Contracts_trTrap W img).toAllocContracts
  decodeErrorFrom := (stage2Contracts_trTrap W img).decode_error_from
  decodeErrorPush := (stage2Contracts_trTrap W img).decode_error_push

theorem cliSignedHooks (W : CliHooks) (img : Obj.Image) :
    SignedHooks img.base E2E.HooksE.A0 (cliExterns W) where
  alloc := allocContracts_cli W img
  decodeErrorFrom := subroutine_ok_cli_of_trTrap (stage2Contracts_trTrap W img).decode_error_from
  decodeErrorPush := subroutine_ok_cli_of_trTrap (stage2Contracts_trTrap W img).decode_error_push

theorem decodeVarint6_ok_trTrap (W : CliHooks) (img : Obj.Image) :
    subroutine_ok (tripleRatchetProgAtExt img.base (trTrapExterns W.C (cliExterns W)))
      ((tripleRatchetProgAtExt img.base (trTrapExterns W.C (cliExterns W))).fnAddr decodeVarint6Name)
      (SpqrV1.Varint.decodeVarint2Spec E2E.HooksE.A0) := by
  let hC := stage2Contracts_trTrap W img
  refine CryptoVerification.CliC.SpqrV1.Varint.decodeVarint2_ok_of_contracts ?_ ?_
  · rw [CryptoVerification.CliC.SpqrV1.Varint.decodeVarint2_add_from_eq_fnAddr]
    exact hC.decode_error_from
  · rw [CryptoVerification.CliC.SpqrV1.Varint.decodeVarint2_add_slow_eq_fnAddr, BitVec.add_zero]
    exact Prost.decodeVarintSlow_ok_of_session2 hC.decode_varint_slow

theorem skipField7_ok_trTrap (W : CliHooks) (img : Obj.Image) :
    subroutine_ok (tripleRatchetProgAtExt img.base (trTrapExterns W.C (cliExterns W)))
      ((tripleRatchetProgAtExt img.base (trTrapExterns W.C (cliExterns W))).fnAddr skipField7Name)
      (SpqrV1.Varint.skipField3Spec E2E.HooksE.A0) := by
  let hC := stage2Contracts_trTrap W img
  refine CryptoVerification.CliC.SpqrV1.Varint.skipField3_ok_of_contracts ?_
    (decodeVarint6_ok_trTrap W img)
  rw [CryptoVerification.CliC.SpqrV1.Varint.skipField3_add_from_eq_fnAddr]
  exact hC.decode_error_from

theorem bytesMerge7_ok_trTrap (W : CliHooks) {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img) :
    subroutine_ok (tripleRatchetProgAtExt img.base (trTrapExterns W.C (cliExterns W)))
      ((tripleRatchetProgAtExt img.base (trTrapExterns W.C (cliExterns W))).fnAddr bytesMerge7Name)
      (SpqrV1.Prost.BytesMerge.bytesMerge3Spec E2E.HooksE.A0 img) := by
  let hC := stage2Contracts_trTrap W img
  exact CryptoVerification.CliC.SpqrV1.Prost.BytesMerge.bytes_merge_3_ok_ext
    himg hC.toAllocContracts hC.decode_error_from
    (subroutine_ok_inImage_of_subroutine_ok img (decodeVarint6_ok_trTrap W img))
    (bytesFromVecOk_ext himg rfl)
    (CryptoVerification.CliC.SpqrV1.Alloc.do_reserve_7_ok_ext hC.toAllocContracts)
    bytesVtableSlotLoaded
    (fun p v => bytesVtableDropOk_ext p v v.length hC.toAllocContracts himg rfl)

theorem cliSignedPortDeps_trTrap (W : CliHooks) {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img) :
    SignedPortDeps img E2E.HooksE.A0 (trTrapExterns W.C (cliExterns W)) where
  decodeVarint6 := decodeVarint6_ok_trTrap W img
  skipField7 := skipField7_ok_trTrap W img
  bytesMerge7 := bytesMerge7_ok_trTrap W himg
  dropDecodeError3 := CryptoVerification.CliC.LibsignalTripleRatchet.Prost.dropDecodeError_ok_ext
    (stage2Contracts_trTrap W img).toAllocContracts

theorem cliSignedPortDeps (W : CliHooks) {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img) :
    SignedPortDeps img E2E.HooksE.A0 (cliExterns W) where
  decodeVarint6 := subroutine_ok_cli_of_trTrap (decodeVarint6_ok_trTrap W img)
  skipField7 := subroutine_ok_cli_of_trTrap (skipField7_ok_trTrap W img)
  bytesMerge7 := subroutine_ok_cli_of_trTrap (bytesMerge7_ok_trTrap W himg)
  dropDecodeError3 := CryptoVerification.CliC.LibsignalTripleRatchet.Prost.dropDecodeError_ok_ext
    (allocContracts_cli W img)

/-! ## 2. `decode_kyber_pre_key` / `decode_signed_pre_key` & Concrete Store Kits -/

theorem cliDecodeKyberPreKey_ok_trTrap (W : CliHooks) {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img) :
    subroutine_ok (tripleRatchetProgAtExt img.base (trTrapExterns W.C (cliExterns W)))
      ((tripleRatchetProgAtExt img.base (trTrapExterns W.C (cliExterns W))).fnAddr
        decodeKyberPreKeyName)
      (decodeKyberPreKeySpec E2E.HooksE.A0 img) := by
  have hb := base_aligned himg
  have d := cliSignedPortDeps_trTrap W himg
  exact DecodeKyberPreKey.decodeKyberPreKey_ok_of_decode
    (SignedPreKeyDecode.signedDecode_ok_of_deps (cliSignedHooks_trTrap W img) d hb)
    d.dropDecodeError3 hb

theorem cliDecodeKyberPreKey_ok (W : CliHooks) {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img) :
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExterns W))
      ((tripleRatchetProgAtExt img.base (cliExterns W)).fnAddr decodeKyberPreKeyName)
      (decodeKyberPreKeySpec E2E.HooksE.A0 img) :=
  subroutine_ok_cli_of_trTrap (cliDecodeKyberPreKey_ok_trTrap W himg)

theorem cliDecodeSignedPreKey_ok (W : CliHooks) {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img) :
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExterns W))
      ((tripleRatchetProgAtExt img.base (cliExterns W)).fnAddr decodeKyberPreKeyName)
      (decodeSignedPreKeySpec E2E.HooksE.A0 img) := by
  rw [SignedAssembly.decodeSignedPreKeySpec_eq]
  exact cliDecodeKyberPreKey_ok W himg

theorem cliSignedPreKeyKitOk_trTrap (W : CliHooks) {img : Obj.Image} {F0 : FsFiles}
    {sid : BitVec 32} {readStk s1 s2 : Nat}
    (himg : Obj.Loads libsignalSessionImage img)
    (hs1 : (cliKitStk ⟨readStk⟩).spkGetShim ≤ s1)
    (hs2 : (cliKitStk ⟨readStk⟩).spkGetPoll ≤ s2) :
    SignedPreKeyStoreKitOkImgE img
      (cliSignedPreKeyStoreSpec E2E.HooksE.A0 img.base cliIo.rd F0 cliWrOk sid s1 s2)
      (trTrapExterns W.C (cliExterns W)) :=
  cliSpkKitOkImgE himg (RunHooks.trTrap W img)
    (cliReadFile_ok_trTrap W img readStk) (cliDecodeKyberPreKey_ok_trTrap W himg) hs1 hs2

theorem cliSignedPreKeyKitOk_ext (W : CliHooks) {img : Obj.Image} {F0 : FsFiles}
    {sid : BitVec 32} {readStk s1 s2 : Nat}
    (himg : Obj.Loads libsignalSessionImage img)
    (hs1 : (cliKitStk ⟨readStk⟩).spkGetShim ≤ s1)
    (hs2 : (cliKitStk ⟨readStk⟩).spkGetPoll ≤ s2) :
    SignedPreKeyStoreKitOkImgE img
      (cliSignedPreKeyStoreSpec E2E.HooksE.A0 img.base cliIo.rd F0 cliWrOk sid s1 s2)
      (cliExterns W) :=
  cliSpkKitOkImgE himg (RunHooks.cli W img)
    (cliReadFile_ok W img readStk) (cliDecodeKyberPreKey_ok W himg) hs1 hs2

theorem cliSignedPreKeyKitOk_kit (W : CliHooks) (ctl : BitVec 64) {img : Obj.Image}
    {F0 : FsFiles} {sid : BitVec 32} {readStk s1 s2 : Nat}
    (himg : Obj.Loads libsignalSessionImage img)
    (hs1 : (cliKitStk ⟨readStk⟩).spkGetShim ≤ s1)
    (hs2 : (cliKitStk ⟨readStk⟩).spkGetPoll ≤ s2) :
    SignedPreKeyStoreKitOkImg img
      (cliSignedPreKeyStoreSpec E2E.HooksE.A0 img.base cliIo.rd F0 cliWrOk sid s1 s2)
      W.C ctl (cliExterns W) := by
  have h := cliSignedPreKeyKitOk_trTrap W (F0 := F0) (sid := sid) himg hs1 hs2
  exact ⟨subroutine_ok_kit_of_trTrap h.getShim, subroutine_ok_kit_of_trTrap h.getPoll,
    subroutine_ok_kit_of_trTrap h.getFutDrop⟩

theorem cliKyberKitOk_trTrap (W : CliHooks) {img : Obj.Image} {F0 : FsFiles}
    {kid ksid : BitVec 32} {kbk : PublicKey} {readStk s1 s2 s3 s4 : Nat}
    (himg : Obj.Loads libsignalSessionImage img)
    (hs1 : (cliKitStk ⟨readStk⟩).kpkGetShim ≤ s1)
    (hs2 : (cliKitStk ⟨readStk⟩).kpkGetPoll ≤ s2)
    (hs3 : (cliKitStk ⟨readStk⟩).kpkMarkShim ≤ s3)
    (hs4 : (cliKitStk ⟨readStk⟩).kpkMarkPoll ≤ s4) :
    KyberPreKeyStoreKitOkImgE img
      (cliKpkStoreSpecFull E2E.HooksE.A0 img.base cliIo.rd F0 cliWrOk kid ksid kbk s1 s2 s3 s4)
      (trTrapExterns W.C (cliExterns W)) :=
  cliKpkKitOkImgE himg (RunHooks.trTrap W img)
    (cliReadFile_ok_trTrap W img readStk) (cliDecodeKyberPreKey_ok_trTrap W himg) hs1 hs2 hs3 hs4

theorem cliKyberKitOk_ext (W : CliHooks) {img : Obj.Image} {F0 : FsFiles}
    {kid ksid : BitVec 32} {kbk : PublicKey} {readStk s1 s2 s3 s4 : Nat}
    (himg : Obj.Loads libsignalSessionImage img)
    (hs1 : (cliKitStk ⟨readStk⟩).kpkGetShim ≤ s1)
    (hs2 : (cliKitStk ⟨readStk⟩).kpkGetPoll ≤ s2)
    (hs3 : (cliKitStk ⟨readStk⟩).kpkMarkShim ≤ s3)
    (hs4 : (cliKitStk ⟨readStk⟩).kpkMarkPoll ≤ s4) :
    KyberPreKeyStoreKitOkImgE img
      (cliKpkStoreSpecFull E2E.HooksE.A0 img.base cliIo.rd F0 cliWrOk kid ksid kbk s1 s2 s3 s4)
      (cliExterns W) :=
  cliKpkKitOkImgE himg (RunHooks.cli W img)
    (cliReadFile_ok W img readStk) (cliDecodeKyberPreKey_ok W himg) hs1 hs2 hs3 hs4

theorem cliKyberKitOk_kit (W : CliHooks) (ctl : BitVec 64) {img : Obj.Image} {F0 : FsFiles}
    {kid ksid : BitVec 32} {kbk : PublicKey} {readStk s1 s2 s3 s4 : Nat}
    (himg : Obj.Loads libsignalSessionImage img)
    (hs1 : (cliKitStk ⟨readStk⟩).kpkGetShim ≤ s1)
    (hs2 : (cliKitStk ⟨readStk⟩).kpkGetPoll ≤ s2)
    (hs3 : (cliKitStk ⟨readStk⟩).kpkMarkShim ≤ s3)
    (hs4 : (cliKitStk ⟨readStk⟩).kpkMarkPoll ≤ s4) :
    KyberPreKeyStoreKitOkImg img
      (cliKpkStoreSpecFull E2E.HooksE.A0 img.base cliIo.rd F0 cliWrOk kid ksid kbk s1 s2 s3 s4)
      W.C ctl (cliExterns W) := by
  have h := cliKyberKitOk_trTrap W (F0 := F0) (kid := kid) (ksid := ksid) (kbk := kbk)
    himg hs1 hs2 hs3 hs4
  exact ⟨subroutine_ok_kit_of_trTrap h.getShim, subroutine_ok_kit_of_trTrap h.getPoll,
    subroutine_ok_kit_of_trTrap h.getFutDrop, subroutine_ok_kit_of_trTrap h.markShim,
    subroutine_ok_kit_of_trTrap h.markPoll, subroutine_ok_kit_of_trTrap h.markFutDrop⟩

/-! ## 3. `PreKeyRecord::deserialize` & Concrete One-Time Pre-Key Store Kits -/

theorem cliPreKeyDeserializeHooks_of_alloc {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    PreKeyDeserialize.Helpers.PreKeyDeserializeHooks img A ext where
  dealloc := hA.dealloc
  decode_varint_slow := SigTryFromHelpers.decodeVarintSlow_ok_ext_x hA
  decode_error_from := SigTryFromHelpers.decodeErrorFrom_ok_ext_x hA
  decode_error_push := SigTryFromHelpers.decodeErrorPush_ok_ext_x hA

theorem cliDecodeDeps_of_alloc {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (C : Crypto)
    (himg : Obj.Loads libsignalSessionImage img) (hA : AllocContractsX img A ext) :
    DecodeDeps img A ext :=
  let td := cliTryFromDeps_ok C 0#64 himg hA
  { varintSlice := td.varintSlice
    int32Merge := td.int32Merge
    skipField := td.skipField
    dropDecodeError := td.dropDecodeError
    bytesMerge := td.bytesMerge
    pkTryFrom := pkTryFrom_ok_ext img ext himg }

theorem cliPreKeyDeserialize_ok_of_alloc {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (C : Crypto)
    (himg : Obj.Loads libsignalSessionImage img) (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName)
      (preKeyDeserializeSpec A img) :=
  PreKeyDeserialize.preKeyDeserialize_ok_of_hooks
    (cliPreKeyDeserializeHooks_of_alloc hA)
    (cliDecodeDeps_of_alloc C himg hA)
    (base_aligned himg)

theorem cliPreKeyDeserialize_ok_trTrap (W : CliHooks) {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img) :
    subroutine_ok (tripleRatchetProgAtExt img.base (trTrapExterns W.C (cliExterns W)))
      ((tripleRatchetProgAtExt img.base (trTrapExterns W.C (cliExterns W))).fnAddr
        preKeyDeserializeName)
      (preKeyDeserializeSpec E2E.HooksE.A0 img) :=
  cliPreKeyDeserialize_ok_of_alloc W.C himg (RunHooks.trTrap W img).alloc

theorem cliPreKeyDeserialize_ok (W : CliHooks) {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img) :
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExterns W))
      ((tripleRatchetProgAtExt img.base (cliExterns W)).fnAddr preKeyDeserializeName)
      (preKeyDeserializeSpec E2E.HooksE.A0 img) :=
  subroutine_ok_cli_of_trTrap (cliPreKeyDeserialize_ok_trTrap W himg)

theorem cliPreKeyKitOk_trTrap (W : CliHooks) {img : Obj.Image} {F0 : FsFiles}
    {pid : BitVec 32} {readStk s1 s2 s3 s4 : Nat}
    (himg : Obj.Loads libsignalSessionImage img)
    (hs1 : (cliKitStk ⟨readStk⟩).pkGetShim ≤ s1)
    (hs2 : (cliKitStk ⟨readStk⟩).pkGetPoll ≤ s2)
    (hs3 : (cliKitStk ⟨readStk⟩).pkRemoveShim ≤ s3)
    (hs4 : (cliKitStk ⟨readStk⟩).pkRemovePoll ≤ s4) :
    PreKeyStoreKitOkImgE img
      (cliPreKeyStoreSpec E2E.HooksE.A0 img.base cliIo.rd F0 cliWrOk pid s1 s2 s3 s4)
      (trTrapExterns W.C (cliExterns W)) :=
  cliPkKitOkImgE himg (RunHooks.trTrap W img)
    (cliReadFile_ok_trTrap W img readStk) (cliPreKeyDeserialize_ok_trTrap W himg)
    hs1 hs2 hs3 hs4

theorem cliPreKeyKitOk_ext (W : CliHooks) {img : Obj.Image} {F0 : FsFiles}
    {pid : BitVec 32} {readStk s1 s2 s3 s4 : Nat}
    (himg : Obj.Loads libsignalSessionImage img)
    (hs1 : (cliKitStk ⟨readStk⟩).pkGetShim ≤ s1)
    (hs2 : (cliKitStk ⟨readStk⟩).pkGetPoll ≤ s2)
    (hs3 : (cliKitStk ⟨readStk⟩).pkRemoveShim ≤ s3)
    (hs4 : (cliKitStk ⟨readStk⟩).pkRemovePoll ≤ s4) :
    PreKeyStoreKitOkImgE img
      (cliPreKeyStoreSpec E2E.HooksE.A0 img.base cliIo.rd F0 cliWrOk pid s1 s2 s3 s4)
      (cliExterns W) :=
  cliPkKitOkImgE himg (RunHooks.cli W img)
    (cliReadFile_ok W img readStk) (cliPreKeyDeserialize_ok W himg) hs1 hs2 hs3 hs4

theorem cliPreKeyKitOk_kit (W : CliHooks) (ctl : BitVec 64) {img : Obj.Image} {F0 : FsFiles}
    {pid : BitVec 32} {readStk s1 s2 s3 s4 : Nat}
    (himg : Obj.Loads libsignalSessionImage img)
    (hs1 : (cliKitStk ⟨readStk⟩).pkGetShim ≤ s1)
    (hs2 : (cliKitStk ⟨readStk⟩).pkGetPoll ≤ s2)
    (hs3 : (cliKitStk ⟨readStk⟩).pkRemoveShim ≤ s3)
    (hs4 : (cliKitStk ⟨readStk⟩).pkRemovePoll ≤ s4) :
    PreKeyStoreKitOkImg img
      (cliPreKeyStoreSpec E2E.HooksE.A0 img.base cliIo.rd F0 cliWrOk pid s1 s2 s3 s4)
      W.C ctl (cliExterns W) := by
  have h := cliPreKeyKitOk_trTrap W (F0 := F0) (pid := pid) himg hs1 hs2 hs3 hs4
  exact ⟨subroutine_ok_kit_of_trTrap h.getShim, subroutine_ok_kit_of_trTrap h.getPoll,
    subroutine_ok_kit_of_trTrap h.getFutDrop, subroutine_ok_kit_of_trTrap h.removeShim,
    subroutine_ok_kit_of_trTrap h.removePoll, subroutine_ok_kit_of_trTrap h.removeFutDrop⟩

/-! ## 4. X-Form / `RunHooksExt` Record Decoders & Store-Kit Instantiations -/

section ExtStoreKits

open CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.SignalSession.Cli.Store

theorem cliSignedPortDepsX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) (hA : AllocContractsX img A ext) :
    SignedPortDepsX img A ext where
  decodeVarint6 :=
    LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.SignedPort7.VarintDrop7.decodeVarint6_ok_of_alloc_x hA
  skipField7 :=
    LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.SignedPort7.SkipField7.skipField7_ok_of_alloc_x hA
  bytesMerge7 :=
    LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.SignedPort7.BytesMerge7.bytesMerge7_ok_of_alloc_x himg hA
  dropDecodeError3 :=
    LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.SignedPort7.VarintDrop7.dropDecodeError3_ok_of_alloc_x hA

theorem cliDecodeKyberPreKey_ok_of_alloc {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr decodeKyberPreKeyName)
      (decodeKyberPreKeySpec A img) :=
  SignedAssembly.decodeKyberPreKey_ok_of_hooks_x
    (SignedHooksX.of_alloc hA) (cliSignedPortDepsX himg hA) (base_aligned himg)

theorem cliDecodeSignedPreKey_ok_of_alloc {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr decodeKyberPreKeyName)
      (decodeSignedPreKeySpec A img) :=
  SignedAssembly.decodeSignedPreKey_ok_of_hooks_x
    (SignedHooksX.of_alloc hA) (cliSignedPortDepsX himg hA) (base_aligned himg)

private theorem dirGet_ok_of_hooksExt {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {rd : ReadRule} {readStk : Nat}
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooksExt img A ext)
    (hRead : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr Cli.readFileName)
      (readFileSpec rd cliWrOk A img readStk)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dirGetName)
      (dirGetSpec rd cliWrOk A img (RunBudgets.dirGetNeed ⟨readStk⟩)) := by
  have hb : (img.base &&& 0xfff#64) = 0#64 := base_aligned himg
  exact Get.dirGet_ok_of_deps_withStack (pathOk := cliWrOk) himg (fun _ hp => hp.2) hh.alloc
    hh.memcpyRO hh.bcmp
    (Path.path_ok_of_deps_withStack hh.alloc hh.memcpyRO
      (reserve_ok_ext hh (Nat.le_refl doReserveStackX)) (Nat.le_refl pathNeed) hb)
    hRead hh.fs (Nat.le_refl (RunBudgets.dirGetNeed ⟨readStk⟩)) hb

private theorem cliMarkErr_of_parts_ext (A : RustAlloc) (out : BitVec 64) (ans : KpkMarkAns)
    (bs : List (BitVec 8)) (w4 w5 : BitVec 64) (tail : SepProp)
    (htail : tail ⊢ match ans with
      | .readErr => ⌜w5 = BitVec.ofNat 64 (utf8 "read").length⌝ ∗ (w4 ↦ᵣ utf8 "read")
      | _ => emp)
    (hne : ans ≠ .ok) :
    ((out ↦₆₄ match ans with | .reused => speWord 24 | _ => speWord 1) ∗
      vecU8 A (out + 8#64) bs ∗
      ((out + 0x20#64) ↦₆₄ w4) ∗ ((out + 0x28#64) ↦₆₄ w5) ∗ tail) ⊢
    ∃∗ r : Except CliKpkMarkErr Unit,
      ⌜(match r with | .ok () => ans = .ok | .error e => ans = e.ans)⌝ ∗
        unitSpePollOutAt (cliKpkMarkErrSpec A) out r := by
  unfold vecU8 vecU8At vecHeader
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun cap => ?_
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun ptr => ?_
  let e : CliKpkMarkErr :=
    { ans := ans, ne_ok := hne, cap := cap, ptr := ptr,
      len := BitVec.ofNat 64 bs.length, w4 := w4, w5 := w5 }
  refine Entails.sepExists_right (.error e) (Entails.pure_right rfl ?_)
  dsimp only [unitSpePollOutAt, speErrAt, speWordsAt, cliKpkMarkErrSpec, e]
  have h10 : out + 8#64 + 8#64 = out + 0x10#64 := by bv_omega
  have h18 : out + 8#64 + 16#64 = out + 0x18#64 := by bv_omega
  rw [h10, h18]
  set bufHeap : SepProp :=
    if cap = 0 then emp
    else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
      memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)
  set w0Term : SepProp := out ↦₆₄ match ans with | .reused => speWord 24 | _ => speWord 1
  have hvec :
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗ bufHeap ⊢
        ∃∗ bs' : List (BitVec 8),
          ⌜BitVec.ofNat 64 bs'.length = BitVec.ofNat 64 bs.length ∧
            bs'.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
          (if cap = 0 then emp
           else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs') ∗
             memRegion (ptr + BitVec.ofNat 64 bs'.length) (cap.toNat - bs'.length)) := by
    refine Entails.pure_left fun ⟨hlen, hcap, hptr⟩ => ?_
    refine Entails.sepExists_right bs ?_
    exact Entails.pure_right ⟨rfl, hlen, hcap, hptr⟩ (Entails.refl _)
  refine Entails.trans (Entails.of_eq (show _ =
    ((w0Term ∗ ((out + 0x08#64) ↦₆₄ cap) ∗ ((out + 0x10#64) ↦₆₄ ptr) ∗
        ((out + 0x18#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        ((out + 0x20#64) ↦₆₄ w4) ∗ ((out + 0x28#64) ↦₆₄ w5)) ∗
      ((⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗ bufHeap) ∗ tail)) by ac_rfl)) ?_
  cases ans <;> exact sepConj_mono_right (sepConj_mono hvec htail)

private theorem cliKpkMarkOut_entails_ext (A : RustAlloc) (out : BitVec 64) (a : KpkMarkAns) :
    kpkMarkOutAt A out a ⊢
      ∃∗ ans : Except CliKpkMarkErr Unit,
        ⌜(match ans with | .ok () => a = .ok | .error e => a = e.ans)⌝ ∗
          unitSpePollOutAt (cliKpkMarkErrSpec A) out ans := by
  rcases a with _ | _ | _ | _
  · exact Entails.sepExists_right (.ok ()) (Entails.pure_right rfl (Entails.refl _))
  · dsimp only [kpkMarkOutAt, speAt, strRefAt]
    have e1 : out + asm64% spePayloadOff = out + 8#64 := by bv_omega
    have e2 : out + asm64% speInvalidStateFnOff = out + 0x20#64 := by bv_omega
    have e3 : out + 0x20#64 + asm64% boxSliceLenOff = out + 0x28#64 := by bv_omega
    rw [e1, e2, e3, sepExists_sepConj_left, sepExists_sepConj_right]
    refine Entails.sepExists_elim fun bs => ?_
    rw [sepExists_sepConj_right, sepExists_sepConj_right]
    refine Entails.sepExists_elim fun p => ?_
    refine Entails.trans (Entails.of_eq (by ac_rfl))
      (cliMarkErr_of_parts_ext A out .readErr bs p
        (BitVec.ofNat 64 (utf8 "read").length) (p ↦ᵣ utf8 "read")
        (Entails.pure_right rfl (Entails.refl _)) (by nofun))
  · dsimp only [kpkMarkOutAt, strSpeAt]
    rw [sepExists_sepConj_left, sepExists_sepConj_right]
    refine Entails.sepExists_elim fun bs => ?_
    rw [ProofLib.memRegion_split' (b := out + 0x20#64) (n := 8) (k := 8)
          (b' := out + 0x28#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_eight, ProofLib.memRegion_eight,
        sepExists_sepConj_left, sepExists_sepConj_right, sepExists_sepConj_right]
    refine Entails.sepExists_elim fun w4 => ?_
    rw [sepExists_sepConj_right, sepExists_sepConj_right, sepExists_sepConj_right]
    refine Entails.sepExists_elim fun w5 => ?_
    rw [← sepConj_emp ((out + 0x28#64) ↦₆₄ w5)]
    refine Entails.trans (Entails.of_eq (by ac_rfl))
      (cliMarkErr_of_parts_ext A out .malformed bs w4 w5 emp (Entails.refl _) (by nofun))
  · dsimp only [kpkMarkOutAt, strSpeAt]
    rw [sepExists_sepConj_left, sepExists_sepConj_right]
    refine Entails.sepExists_elim fun bs => ?_
    rw [ProofLib.memRegion_split' (b := out + 0x20#64) (n := 8) (k := 8)
          (b' := out + 0x28#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_eight, ProofLib.memRegion_eight,
        sepExists_sepConj_left, sepExists_sepConj_right, sepExists_sepConj_right]
    refine Entails.sepExists_elim fun w4 => ?_
    rw [sepExists_sepConj_right, sepExists_sepConj_right, sepExists_sepConj_right]
    refine Entails.sepExists_elim fun w5 => ?_
    rw [← sepConj_emp ((out + 0x28#64) ↦₆₄ w5)]
    refine Entails.trans (Entails.of_eq (by ac_rfl))
      (cliMarkErr_of_parts_ext A out .reused bs w4 w5 emp (Entails.refl _) (by nofun))

/-- `RunHooksExt`-generalized `PreKeyStoreKitOkImgE` assembly for `cliPreKeyStoreSpec`. -/
theorem cliPkKitOkImgE_of_hooksExt {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {rd : ReadRule} {F0 : FsFiles} {pid : BitVec 32} {readStk s1 s2 s3 s4 : Nat}
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooksExt img A ext)
    (hRead : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr Cli.readFileName)
      (readFileSpec rd cliWrOk A img readStk))
    (hPkDec : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName)
      (preKeyDeserializeSpec A img))
    (hs1 : (cliKitStk ⟨readStk⟩).pkGetShim ≤ s1)
    (hs2 : (cliKitStk ⟨readStk⟩).pkGetPoll ≤ s2)
    (hs3 : (cliKitStk ⟨readStk⟩).pkRemoveShim ≤ s3)
    (hs4 : (cliKitStk ⟨readStk⟩).pkRemovePoll ≤ s4) :
    PreKeyStoreKitOkImgE img
      (cliPreKeyStoreSpec A img.base rd F0 cliWrOk pid s1 s2 s3 s4) ext := by
  have hb : (img.base &&& 0xfff#64) = 0#64 := base_aligned himg
  have hC : AllocContractsX img A ext := hh.alloc
  have hDecimal := Decimal.decimal_ok_of_deps
    (reserve_ok_ext hh (Nat.le_refl doReserveStackX)) (Nat.le_refl SessKit.decNeed) hb
  have hGet := dirGet_ok_of_hooksExt himg hh hRead
  have hGrow := GrowOne.growOneDir_ok_x hC (Nat.le_refl SessKit.growOneDirNeed) hb
  have hPut := Put.dirPut_ok_of_deps hC hh.bcmp hGrow (Nat.le_refl SessKit.dirPutNeed) hb
  have hDropW := DropSpeWord.dropSpeWord_ok himg hC
  refine ⟨?_, ?_, cliIdFutDrop_inImage_ext, ?_, ?_, cliIdFutDrop_inImage_ext⟩
  · have h := PkShims.pkGetShim_ok_of_deps hC hs1 hb
    rw [cliPkGetShim_fnAddr] at h
    exact pkShim_conseq h
  · have h := PkGetPoll.pkGetPoll_ok_of_deps hC hDecimal hGet hPkDec hDropW hh.fs hs2 hb
    rw [cliPkGetPoll_fnAddr] at h
    refine subroutine_ok_map_panic h ?_
    rintro ⟨⟨fut, out, self, id⟩, st0⟩ R s0 hpre
    dsimp only [kitPreKeyGetPollSpecE, Spec.inImage, withEnvPre, kitPreKeyGetPollSpec,
      cliPreKeyStoreSpec, cliPkStoreAt] at hpre
    have hpre' : s0.mem ⊨
        ⌜img.FrozenLoaded s0 ∧ s0.symtab = img.symtab⌝ ∗
        (⌜s0.fs.files = F0⌝ ∗
        (⌜(img.base &&& 0xfff#64) = 0#64 ∧ s0.readReg64 .x0 = fut ∧ s0.readReg64 .x8 = out ∧
          id = pid⌝ ∗
        (⌜CliPkInv rd F0 cliWrOk pid st0⌝ ∗
        (pkBoxAt fut self id 0#8 ∗ dirAt A self st0 ∗ memRegion out 56 ∗
          A.pool ∗ stackAt s0.sp s2 ∗ R)))) :=
      Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) hpre
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hfl, hpre'⟩ := hpre'
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hfiles, hpre'⟩ := hpre'
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨⟨_, hx0, hx8, hid⟩, hpre'⟩ := hpre'
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hinv, hsp⟩ := hpre'
    subst hid
    have hm_hop : s0.mem ⊨ (pkGetPollSpec rd cliWrOk A img s2).pre ⟨fut, out, self, id, st0⟩ s0 ∗ R := by
      dsimp only [pkGetPollSpec, pkGetPollSpecOf, Spec.inImage]
      have h1 : s0.mem ⊨
          ⌜img.FrozenLoaded s0 ∧ s0.symtab = img.symtab⌝ ∗
          (⌜s0.readReg64 .x0 = fut ∧ s0.readReg64 .x8 = out ∧
            PkNameOk cliWrOk st0 id ∧ PkSizeOk rd s0.fs.files st0 id⌝ ∗
          (pkBoxAt fut self id 0#8 ∗ dirAt A self st0 ∗ memRegion out 56 ∗
            A.pool ∗ stackAt s0.sp s2 ∗ R)) := by
        rw [satisfies_pure_sepConj]; refine ⟨hfl, ?_⟩
        rw [satisfies_pure_sepConj]; exact ⟨⟨hx0, hx8, hinv.nameOk, hfiles ▸ hinv.sizeOk⟩, hsp⟩
      exact Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) h1
    refine ⟨⟨fut, out, self, id, st0⟩, R, hm_hop, ?_, fun _ hp => hp⟩
    intro sf hpost
    dsimp only [pkGetPollSpec, pkGetPollSpecOf, Spec.inImage] at hpost
    simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc,
      satisfies_pure_sepConj] at hpost
    obtain ⟨pa, ⟨hpa, htr⟩, hm⟩ := hpost
    rw [hfiles] at hpa; subst hpa
    have hm' := Satisfies.mono
      (sepConj_mono_left (pkGetAnsAt_entails_pollOut A img.base rd F0 cliWrOk id s1 s2 s3 s4 st0 id out)) hm
    simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc,
      satisfies_pure_sepConj] at hm'
    obtain ⟨ans, hrel, hm'⟩ := hm'
    dsimp only [kitPreKeyGetPollSpecE, Spec.inImage, withEnvPre, kitPreKeyGetPollSpec]
    simp only [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨ans, ?_⟩
    have hstore :
        (cliPreKeyStoreSpec A img.base rd F0 cliWrOk id s1 s2 s3 s4).storeAt self
          ((cliPreKeyStoreSpec A img.base rd F0 cliWrOk id s1 s2 s3 s4).getUpdate st0 id ans) =
        (⌜CliPkInv rd F0 cliWrOk id st0⌝ ∗ dirAt A self st0) := rfl
    have hstk : (cliPreKeyStoreSpec A img.base rd F0 cliWrOk id s1 s2 s3 s4).getPollStack = s2 := rfl
    have hbox : (cliPreKeyStoreSpec A img.base rd F0 cliWrOk id s1 s2 s3 s4).getBoxAt fut self id 1#8 =
        pkBoxAt fut self id 1#8 := rfl
    rw [hstore, hstk, hbox]
    have hgoal : sf.mem ⊨
        ⌜(cliPreKeyStoreSpec A img.base rd F0 cliWrOk id s1 s2 s3 s4).getRel st0 id ans ∧
          sf.trace = s0.trace ++ []⌝ ∗
        (⌜CliPkInv rd F0 cliWrOk id st0⌝ ∗
          (preKeyGetPollOutAt (cliPreKeyStoreSpec A img.base rd F0 cliWrOk id s1 s2 s3 s4) out ans ∗
            pkBoxAt fut self id 1#8 ∗ dirAt A self st0 ∗ A.pool ∗ stackAt s0.sp s2 ∗ R)) := by
      rw [satisfies_pure_sepConj]; refine ⟨⟨hrel, by rw [List.append_nil]; exact htr⟩, ?_⟩
      rw [satisfies_pure_sepConj]; exact ⟨hinv, Eq.mp (congrArg (sf.mem ⊨ ·) (by ac_rfl)) hm'⟩
    exact Eq.mp (congrArg (sf.mem ⊨ ·) (by ac_rfl)) hgoal
  · have h := PkShims.pkRemoveShim_ok_of_deps hC hs3 hb
    rw [cliPkRemoveShim_fnAddr] at h
    exact pkShim_conseq h
  · have h := PkRemovePoll.pkRemovePoll_ok_of_deps hC hDecimal hGet hPut hh.fs hs4 hb
    rw [cliPkRemovePoll_fnAddr] at h
    refine subroutine_ok_map_panic h ?_
    rintro ⟨⟨fut, out, self, id⟩, st0⟩ R s0 hpre
    dsimp only [kitPreKeyRemovePollSpecE, Spec.inImage, withEnvPre, kitPreKeyRemovePollSpec,
      cliPreKeyStoreSpec, cliPkStoreAt] at hpre
    have hpre' : s0.mem ⊨
        ⌜img.FrozenLoaded s0 ∧ s0.symtab = img.symtab⌝ ∗
        (⌜s0.fs.files = F0⌝ ∗
        (⌜(img.base &&& 0xfff#64) = 0#64 ∧ s0.readReg64 .x0 = fut ∧ s0.readReg64 .x8 = out ∧
          id = pid⌝ ∗
        (⌜CliPkInv rd F0 cliWrOk pid st0⌝ ∗
        (pkBoxAt fut self id 0#8 ∗ dirAt A self st0 ∗ memRegion out 48 ∗
          A.pool ∗ stackAt s0.sp s4 ∗ R)))) :=
      Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) hpre
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hfl, hpre'⟩ := hpre'
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hfiles, hpre'⟩ := hpre'
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨⟨_, hx0, hx8, hid⟩, hpre'⟩ := hpre'
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hinv, hsp⟩ := hpre'
    subst hid
    have hm_hop : s0.mem ⊨ (pkRemovePollSpec rd cliWrOk A img s4).pre ⟨fut, out, self, id, st0⟩ s0 ∗ R := by
      dsimp only [pkRemovePollSpec, Spec.inImage]
      have h1 : s0.mem ⊨
          ⌜img.FrozenLoaded s0 ∧ s0.symtab = img.symtab⌝ ∗
          (⌜s0.readReg64 .x0 = fut ∧ s0.readReg64 .x8 = out ∧
            PkNameOk cliWrOk st0 id ∧ st0.changed.length < 2 ^ 32⌝ ∗
          (pkBoxAt fut self id 0#8 ∗ dirAt A self st0 ∗ memRegion out 48 ∗
            A.pool ∗ stackAt s0.sp s4 ∗ R)) := by
        rw [satisfies_pure_sepConj]; refine ⟨hfl, ?_⟩
        rw [satisfies_pure_sepConj]; exact ⟨⟨hx0, hx8, hinv.nameOk, hinv.oneLt.1⟩, hsp⟩
      exact Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) h1
    refine ⟨⟨fut, out, self, id, st0⟩, R, hm_hop, ?_, fun _ hp => hp⟩
    intro sf hpost
    dsimp only [pkRemovePollSpec, Spec.inImage] at hpost
    simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc,
      satisfies_pure_sepConj] at hpost
    obtain ⟨res, ⟨hres, htr⟩, hm⟩ := hpost
    rw [hfiles] at hres; subst hres
    have hm' := Satisfies.mono
      (sepConj_mono_left (pkRemoveOutAt_entails_pollOut A img.base rd F0 cliWrOk id s1 s2 s3 s4 st0 id out)) hm
    simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc,
      satisfies_pure_sepConj] at hm'
    obtain ⟨ans, ⟨hrel, heq2⟩, hm'⟩ := hm'
    rw [heq2] at hm'
    dsimp only [kitPreKeyRemovePollSpecE, Spec.inImage, withEnvPre, kitPreKeyRemovePollSpec]
    simp only [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨ans, ?_⟩
    have hstore :
        (cliPreKeyStoreSpec A img.base rd F0 cliWrOk id s1 s2 s3 s4).storeAt self
          ((cliPreKeyStoreSpec A img.base rd F0 cliWrOk id s1 s2 s3 s4).removeUpdate st0 id ans) =
        (⌜CliPkInv rd F0 cliWrOk id
            (_root_.CryptoVerification.SignalSession.Cli.removePreKey rd F0 st0 id).2⌝ ∗
          dirAt A self (_root_.CryptoVerification.SignalSession.Cli.removePreKey rd F0 st0 id).2) := rfl
    have hstk : (cliPreKeyStoreSpec A img.base rd F0 cliWrOk id s1 s2 s3 s4).removePollStack = s4 := rfl
    have hbox : (cliPreKeyStoreSpec A img.base rd F0 cliWrOk id s1 s2 s3 s4).removeBoxAt fut self id 1#8 =
        pkBoxAt fut self id 1#8 := rfl
    rw [hstore, hstk, hbox]
    have hgoal : sf.mem ⊨
        ⌜(cliPreKeyStoreSpec A img.base rd F0 cliWrOk id s1 s2 s3 s4).removeRel st0 id ans ∧
          sf.trace = s0.trace ++ []⌝ ∗
        (⌜CliPkInv rd F0 cliWrOk id
            (_root_.CryptoVerification.SignalSession.Cli.removePreKey rd F0 st0 id).2⌝ ∗
          (preKeyRemovePollOutAt (cliPreKeyStoreSpec A img.base rd F0 cliWrOk id s1 s2 s3 s4) out ans ∗
            dirAt A self (_root_.CryptoVerification.SignalSession.Cli.removePreKey rd F0 st0 id).2 ∗
            pkBoxAt fut self id 1#8 ∗ A.pool ∗ stackAt s0.sp s4 ∗ R)) := by
      rw [satisfies_pure_sepConj]; refine ⟨⟨hrel, by rw [List.append_nil]; exact htr⟩, ?_⟩
      rw [satisfies_pure_sepConj]; exact ⟨hinv.removePreKey, Eq.mp (congrArg (sf.mem ⊨ ·) (by ac_rfl)) hm'⟩
    exact Eq.mp (congrArg (sf.mem ⊨ ·) (by ac_rfl)) hgoal

/-- `RunHooksExt`-generalized `SignedPreKeyStoreKitOkImgE` assembly for `cliSignedPreKeyStoreSpec`. -/
theorem cliSpkKitOkImgE_of_hooksExt {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {rd : ReadRule} {F0 : FsFiles} {sid : BitVec 32} {readStk s1 s2 : Nat}
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooksExt img A ext)
    (hRead : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr Cli.readFileName)
      (readFileSpec rd cliWrOk A img readStk))
    (hKpkDec : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr decodeKyberPreKeyName)
      (decodeKyberPreKeySpec A img))
    (hs1 : (cliKitStk ⟨readStk⟩).spkGetShim ≤ s1)
    (hs2 : (cliKitStk ⟨readStk⟩).spkGetPoll ≤ s2) :
    SignedPreKeyStoreKitOkImgE img
      (cliSignedPreKeyStoreSpec A img.base rd F0 cliWrOk sid s1 s2) ext := by
  have hb : (img.base &&& 0xfff#64) = 0#64 := base_aligned himg
  have hC : AllocContractsX img A ext := hh.alloc
  have hDecimal := Decimal.decimal_ok_of_deps
    (reserve_ok_ext hh (Nat.le_refl doReserveStackX)) (Nat.le_refl SessKit.decNeed) hb
  have hGet := dirGet_ok_of_hooksExt himg hh hRead
  have hDropW := DropSpeWord.dropSpeWord_ok himg hC
  have hSpkDec : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr decodeKyberPreKeyName)
      (decodeSignedPreKeySpec A img) :=
    SignedAssembly.decodeSignedPreKeySpec_eq A img ▸ hKpkDec
  refine ⟨?_, ?_, cliIdFutDrop_inImage_ext⟩
  · have h := PkShims.spkGetShim_ok_of_deps hC hs1 hb
    rw [cliSpkGetShim_fnAddr] at h
    exact pkShim_conseq h
  · have h := SpkGetPoll.spkGetPoll_ok_of_deps hC hDecimal hGet hSpkDec hDropW hh.fs hs2 hb
    rw [cliSpkGetPoll_fnAddr] at h
    refine subroutine_ok_map_panic h ?_
    rintro ⟨⟨fut, out, self, id⟩, st0⟩ R (s0 : State) hpre
    dsimp only [kitSpkGetPollSpecE, Spec.inImage, withEnvPre, kitSpkGetPollSpec,
      cliSignedPreKeyStoreSpec, cliSpkStoreAt] at hpre
    have hpre' : s0.mem ⊨
        ⌜img.FrozenLoaded s0 ∧ s0.symtab = img.symtab⌝ ∗
        (⌜s0.fs.files = F0⌝ ∗
        (⌜(img.base &&& 0xfff#64) = 0#64 ∧ s0.readReg64 .x0 = fut ∧ s0.readReg64 .x8 = out ∧
          id = sid⌝ ∗
        (⌜CliSpkInv rd F0 cliWrOk sid st0⌝ ∗
        (pkBoxAt fut self id 0#8 ∗ dirAt A self st0 ∗ memRegion out 88 ∗
          A.pool ∗ stackAt s0.sp s2 ∗ R)))) :=
      Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) hpre
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hfl, hpre'⟩ := hpre'
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hfiles, hpre'⟩ := hpre'
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨⟨_, hx0, hx8, hid⟩, hpre'⟩ := hpre'
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hinv, hsp⟩ := hpre'
    subst hid
    have hm_hop : s0.mem ⊨ (spkGetPollSpec rd cliWrOk A img s2).pre ⟨fut, out, self, id, st0⟩ s0 ∗ R := by
      dsimp only [spkGetPollSpec, pkGetPollSpecOf, Spec.inImage]
      have h1 : s0.mem ⊨
          ⌜img.FrozenLoaded s0 ∧ s0.symtab = img.symtab⌝ ∗
          (⌜s0.readReg64 .x0 = fut ∧ s0.readReg64 .x8 = out ∧
            PkNameOk cliWrOk st0 id ∧ PkSizeOk rd s0.fs.files st0 id⌝ ∗
          (pkBoxAt fut self id 0#8 ∗ dirAt A self st0 ∗ memRegion out 88 ∗
            A.pool ∗ stackAt s0.sp s2 ∗ R)) := by
        rw [satisfies_pure_sepConj]; refine ⟨hfl, ?_⟩
        rw [satisfies_pure_sepConj]; exact ⟨⟨hx0, hx8, hinv.nameOk, hfiles ▸ hinv.sizeOk⟩, hsp⟩
      exact Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) h1
    refine ⟨⟨fut, out, self, id, st0⟩, R, hm_hop, ?_, fun _ hp => hp⟩
    intro sf hpost
    dsimp only [spkGetPollSpec, pkGetPollSpecOf, Spec.inImage] at hpost
    simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc,
      satisfies_pure_sepConj] at hpost
    obtain ⟨pa, ⟨hpa, htr⟩, hm⟩ := hpost
    rw [hfiles] at hpa; subst hpa
    have hm' := Satisfies.mono
      (sepConj_mono_left (spkAnsAt_entails_pollOut A img.base rd F0 cliWrOk id s1 s2 st0 id out)) hm
    simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc,
      satisfies_pure_sepConj] at hm'
    obtain ⟨ans, hrel, hm'⟩ := hm'
    dsimp only [kitSpkGetPollSpecE, Spec.inImage, withEnvPre, kitSpkGetPollSpec]
    simp only [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨ans, ?_⟩
    have hstore :
        (cliSignedPreKeyStoreSpec A img.base rd F0 cliWrOk id s1 s2).storeAt self
          ((cliSignedPreKeyStoreSpec A img.base rd F0 cliWrOk id s1 s2).getUpdate st0 id ans) =
        (⌜CliSpkInv rd F0 cliWrOk id st0⌝ ∗ dirAt A self st0) := rfl
    have hstk : (cliSignedPreKeyStoreSpec A img.base rd F0 cliWrOk id s1 s2).getPollStack = s2 := rfl
    have hbox : (cliSignedPreKeyStoreSpec A img.base rd F0 cliWrOk id s1 s2).getBoxAt fut self id 1#8 =
        pkBoxAt fut self id 1#8 := rfl
    rw [hstore, hstk, hbox]
    have hgoal : sf.mem ⊨
        ⌜(cliSignedPreKeyStoreSpec A img.base rd F0 cliWrOk id s1 s2).getRel st0 id ans ∧
          sf.trace = s0.trace ++ []⌝ ∗
        (⌜CliSpkInv rd F0 cliWrOk id st0⌝ ∗
          (spkGetPollOutAt (cliSignedPreKeyStoreSpec A img.base rd F0 cliWrOk id s1 s2) out ans ∗
            pkBoxAt fut self id 1#8 ∗ dirAt A self st0 ∗ A.pool ∗ stackAt s0.sp s2 ∗ R)) := by
      rw [satisfies_pure_sepConj]; refine ⟨⟨hrel, by rw [List.append_nil]; exact htr⟩, ?_⟩
      rw [satisfies_pure_sepConj]; exact ⟨hinv, Eq.mp (congrArg (sf.mem ⊨ ·) (by ac_rfl)) hm'⟩
    exact Eq.mp (congrArg (sf.mem ⊨ ·) (by ac_rfl)) hgoal

/-- `RunHooksExt`-generalized `KyberPreKeyStoreKitOkImgE` assembly for `cliKpkStoreSpecFull`. -/
theorem cliKpkKitOkImgE_of_hooksExt {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {rd : ReadRule} {F0 : FsFiles} {kid ksid : BitVec 32} {kbk : PublicKey}
    {readStk s1 s2 s3 s4 : Nat}
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooksExt img A ext)
    (hRead : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr Cli.readFileName)
      (readFileSpec rd cliWrOk A img readStk))
    (hKpkDec : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr decodeKyberPreKeyName)
      (decodeKyberPreKeySpec A img))
    (hs1 : (cliKitStk ⟨readStk⟩).kpkGetShim ≤ s1)
    (hs2 : (cliKitStk ⟨readStk⟩).kpkGetPoll ≤ s2)
    (hs3 : (cliKitStk ⟨readStk⟩).kpkMarkShim ≤ s3)
    (hs4 : (cliKitStk ⟨readStk⟩).kpkMarkPoll ≤ s4) :
    KyberPreKeyStoreKitOkImgE img
      (cliKpkStoreSpecFull A img.base rd F0 cliWrOk kid ksid kbk s1 s2 s3 s4) ext := by
  have hb : (img.base &&& 0xfff#64) = 0#64 := base_aligned himg
  have hC : AllocContractsX img A ext := hh.alloc
  have hDecimal := Decimal.decimal_ok_of_deps
    (reserve_ok_ext hh (Nat.le_refl doReserveStackX)) (Nat.le_refl SessKit.decNeed) hb
  have hGet := dirGet_ok_of_hooksExt himg hh hRead
  have hGrow := GrowOne.growOneDir_ok_x hC (Nat.le_refl SessKit.growOneDirNeed) hb
  have hPut := Put.dirPut_ok_of_deps hC hh.bcmp hGrow (Nat.le_refl SessKit.dirPutNeed) hb
  refine ⟨?_, ?_, cliIdFutDrop_inImage_ext, ?_, ?_, cliIdFutDrop_inImage_ext⟩
  · have h := PkShims.kpkGetShim_ok_of_deps hC hs1 hb
    rw [cliKpkGetShim_fnAddr] at h
    exact pkShim_conseq h
  · have h := KpkGetPoll.kpkGetPoll_ok_of_deps hC hDecimal hGet hKpkDec hh.fs hs2 hb
    rw [cliKpkGetPoll_fnAddr] at h
    refine subroutine_ok_map_panic h ?_
    rintro ⟨⟨fut, out, self, id⟩, st0⟩ R (s0 : State) hpre
    dsimp only [kitKpkGetPollSpecE, Spec.inImage, withEnvPre, kitKpkGetPollSpec,
      cliKpkStoreSpecFull, cliKyberPreKeyStoreSpec, cliKpkStoreSpec, cliKpkGetSide,
      cliKpkStoreAtFull] at hpre
    have hpre' : s0.mem ⊨
        ⌜img.FrozenLoaded s0 ∧ s0.symtab = img.symtab⌝ ∗
        (⌜s0.fs.files = F0⌝ ∗
        (⌜(img.base &&& 0xfff#64) = 0#64 ∧ s0.readReg64 .x0 = fut ∧ s0.readReg64 .x8 = out ∧
          id = kid⌝ ∗
        (⌜CliKpkInvFull rd F0 cliWrOk kid ksid kbk st0⌝ ∗
        (pkBoxAt fut self id 0#8 ∗ dirAt A self st0.oneTime ∗
          dirAt A (self + 0x28#64) st0.lastResort ∗ memRegion out 88 ∗
          A.pool ∗ stackAt s0.sp s2 ∗ R)))) :=
      Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) hpre
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hfl, hpre'⟩ := hpre'
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hfiles, hpre'⟩ := hpre'
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨⟨_, hx0, hx8, hid⟩, hpre'⟩ := hpre'
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hinv, hsp⟩ := hpre'
    subst hid
    have hm_hop : s0.mem ⊨ (kpkGetPollSpec rd cliWrOk A img s2).pre ⟨fut, out, self, id, st0⟩ s0 ∗ R := by
      dsimp only [kpkGetPollSpec, Spec.inImage]
      have h1 : s0.mem ⊨
          ⌜img.FrozenLoaded s0 ∧ s0.symtab = img.symtab⌝ ∗
          (⌜s0.readReg64 .x0 = fut ∧ s0.readReg64 .x8 = out ∧
            PkNameOk cliWrOk st0.oneTime id ∧ PkNameOk cliWrOk st0.lastResort id ∧
            PkSizeOk rd s0.fs.files st0.oneTime id ∧ PkSizeOk rd s0.fs.files st0.lastResort id⌝ ∗
          (pkBoxAt fut self id 0#8 ∗ dirAt A self st0.oneTime ∗
            dirAt A (self + 0x28#64) st0.lastResort ∗ memRegion out 88 ∗
            A.pool ∗ stackAt s0.sp s2 ∗ R)) := by
        rw [satisfies_pure_sepConj]; refine ⟨hfl, ?_⟩
        rw [satisfies_pure_sepConj]
        exact ⟨⟨hx0, hx8, hinv.markInv.nameOk, hinv.lastNameOk,
          hfiles ▸ hinv.oneSizeOk, hfiles ▸ hinv.lastSizeOk⟩, hsp⟩
      exact Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) h1
    refine ⟨⟨fut, out, self, id, st0⟩, R, hm_hop, ?_, fun _ hp => hp⟩
    intro sf hpost
    dsimp only [kpkGetPollSpec, Spec.inImage] at hpost
    simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc,
      satisfies_pure_sepConj] at hpost
    obtain ⟨pa, ⟨hpa, htr⟩, hm⟩ := hpost
    rw [hfiles] at hpa; subst hpa
    have hm' := Satisfies.mono
      (sepConj_mono_left (kpkAnsAt_entails_pollOut A img.base rd F0 cliWrOk id ksid kbk
        s1 s2 s3 s4 pkBoxAt_memRegion kpkMarkBoxAt_memRegion st0 id out)) hm
    simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc,
      satisfies_pure_sepConj] at hm'
    obtain ⟨ans, hrel, hm'⟩ := hm'
    dsimp only [kitKpkGetPollSpecE, Spec.inImage, withEnvPre, kitKpkGetPollSpec]
    simp only [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨ans, ?_⟩
    have hstore :
        (cliKpkStoreSpecFull A img.base rd F0 cliWrOk id ksid kbk s1 s2 s3 s4).storeAt self
          ((cliKpkStoreSpecFull A img.base rd F0 cliWrOk id ksid kbk s1 s2 s3 s4).getUpdate st0 id ans) =
        (⌜CliKpkInvFull rd F0 cliWrOk id ksid kbk st0⌝ ∗
          dirAt A self st0.oneTime ∗ dirAt A (self + 0x28#64) st0.lastResort) := rfl
    have hstk :
        (cliKpkStoreSpecFull A img.base rd F0 cliWrOk id ksid kbk s1 s2 s3 s4).getPollStack = s2 := rfl
    have hbox :
        (cliKpkStoreSpecFull A img.base rd F0 cliWrOk id ksid kbk s1 s2 s3 s4).getBoxAt fut self id 1#8 =
        pkBoxAt fut self id 1#8 := rfl
    have hout :
        kpkGetPollOutAt (cliKpkStoreSpecFull A img.base rd F0 cliWrOk id ksid kbk s1 s2 s3 s4) out ans =
        kpkGetPollOutAt
          (cliKpkStoreSpec A img.base rd F0 cliWrOk id ksid kbk (cliKpkGetSide A rd F0 cliWrOk id)
            s1 s2 s3 s4 pkBoxAt_memRegion kpkMarkBoxAt_memRegion)
          out ans := by cases ans <;> rfl
    rw [hstore, hstk, hbox, hout]
    have hgoal : sf.mem ⊨
        ⌜(cliKpkStoreSpecFull A img.base rd F0 cliWrOk id ksid kbk s1 s2 s3 s4).getRel st0 id ans ∧
          sf.trace = s0.trace ++ []⌝ ∗
        (⌜CliKpkInvFull rd F0 cliWrOk id ksid kbk st0⌝ ∗
          (kpkGetPollOutAt
              (cliKpkStoreSpec A img.base rd F0 cliWrOk id ksid kbk (cliKpkGetSide A rd F0 cliWrOk id)
                s1 s2 s3 s4 pkBoxAt_memRegion kpkMarkBoxAt_memRegion)
              out ans ∗
            pkBoxAt fut self id 1#8 ∗ dirAt A self st0.oneTime ∗
            dirAt A (self + 0x28#64) st0.lastResort ∗ A.pool ∗ stackAt s0.sp s2 ∗ R)) := by
      rw [satisfies_pure_sepConj]; refine ⟨⟨hrel, by rw [List.append_nil]; exact htr⟩, ?_⟩
      rw [satisfies_pure_sepConj]; exact ⟨hinv, Eq.mp (congrArg (sf.mem ⊨ ·) (by ac_rfl)) hm'⟩
    exact Eq.mp (congrArg (sf.mem ⊨ ·) (by ac_rfl)) hgoal
  · have h := PkShims.kpkMarkShim_ok_of_deps hC hs3 hb
    rw [cliKpkMarkShim_fnAddr] at h
    exact kpkMarkShim_conseq h
  · have h := KpkMarkPoll.kpkMarkPoll_ok_of_deps himg hC hh.bcmp hDecimal hGet hPut hh.fs hs4 hb
    rw [cliKpkMarkPoll_fnAddr] at h
    refine subroutine_ok_map_panic h ?_
    rintro ⟨⟨fut, out, self, baseKeyA, id, sid, bk⟩, st0⟩ R (s0 : State) hpre
    dsimp only [kitKpkMarkPollSpecE, Spec.inImage, withEnvPre, kitKpkMarkPollSpec,
      cliKpkStoreSpecFull, cliKyberPreKeyStoreSpec, cliKpkStoreSpec, cliKpkStoreAtFull] at hpre
    have hpre' : s0.mem ⊨
        ⌜img.FrozenLoaded s0 ∧ s0.symtab = img.symtab⌝ ∗
        (⌜s0.fs.files = F0⌝ ∗
        (⌜(img.base &&& 0xfff#64) = 0#64 ∧ s0.readReg64 .x0 = fut ∧ s0.readReg64 .x8 = out ∧
          (id = kid ∧ sid = ksid ∧ bk = kbk)⌝ ∗
        (⌜CliKpkInvFull rd F0 cliWrOk kid ksid kbk st0⌝ ∗
        (kpkMarkBoxAt fut self baseKeyA id sid 0#8 ∗ dirAt A self st0.oneTime ∗
          dirAt A (self + 0x28#64) st0.lastResort ∗ memRegion out 48 ∗
          (baseKeyA ↦ₛ bk.bytes.toList) ∗ A.pool ∗ stackAt s0.sp s4 ∗ R)))) :=
      Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) hpre
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hfl, hpre'⟩ := hpre'
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hfiles, hpre'⟩ := hpre'
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨⟨_, hx0, hx8, hid, hsid, hbk⟩, hpre'⟩ := hpre'
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hinv, hsp⟩ := hpre'
    subst hid; subst hsid; subst hbk
    have hm_hop : s0.mem ⊨
        (kpkMarkPollSpec rd cliWrOk A img s4).pre ⟨fut, out, self, baseKeyA, id, sid, bk, st0⟩ s0 ∗ R := by
      dsimp only [kpkMarkPollSpec, Spec.inImage]
      have h1 : s0.mem ⊨
          ⌜img.FrozenLoaded s0 ∧ s0.symtab = img.symtab⌝ ∗
          (⌜s0.readReg64 .x0 = fut ∧ s0.readReg64 .x8 = out ∧
            PkNameOk cliWrOk st0.oneTime id ∧ KpkBaseKeysOk cliWrOk st0.lastResort id ∧
            KpkSeenOk rd s0.fs.files st0.lastResort id sid bk ∧
            st0.oneTime.changed.length < 2 ^ 32 ∧ st0.lastResort.changed.length < 2 ^ 32⌝ ∗
          (kpkMarkBoxAt fut self baseKeyA id sid 0#8 ∗ dirAt A self st0.oneTime ∗
            dirAt A (self + 0x28#64) st0.lastResort ∗ (baseKeyA ↦ₛ bk.bytes.toList) ∗
            memRegion out 48 ∗ A.pool ∗ stackAt s0.sp s4 ∗ R)) := by
        rw [satisfies_pure_sepConj]; refine ⟨hfl, ?_⟩
        rw [satisfies_pure_sepConj]
        exact ⟨⟨hx0, hx8, hinv.markInv.nameOk, hinv.markInv.baseOk,
          hfiles ▸ hinv.markInv.seenOk, hinv.markInv.oneLt.1, hinv.markInv.lastLt.1⟩,
          Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) hsp⟩
      exact Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) h1
    refine ⟨⟨fut, out, self, baseKeyA, id, sid, bk, st0⟩, R, hm_hop, ?_, fun _ hp => hp⟩
    intro sf hpost
    dsimp only [kpkMarkPollSpec, Spec.inImage] at hpost
    simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc,
      satisfies_pure_sepConj] at hpost
    obtain ⟨res, ⟨hres, htr⟩, hm⟩ := hpost
    rw [hfiles] at hres; subst hres
    set m := kpkMarkOf rd F0 st0 id sid bk
    have hm' := Satisfies.mono (sepConj_mono_left (cliKpkMarkOut_entails_ext A out m.1)) hm
    simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc,
      satisfies_pure_sepConj] at hm'
    obtain ⟨ans, hrel, hm'⟩ := hm'
    dsimp only [kitKpkMarkPollSpecE, Spec.inImage, withEnvPre, kitKpkMarkPollSpec]
    simp only [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨ans, ?_⟩
    have hstore :
        (cliKpkStoreSpecFull A img.base rd F0 cliWrOk id sid bk s1 s2 s3 s4).storeAt self
          ((cliKpkStoreSpecFull A img.base rd F0 cliWrOk id sid bk s1 s2 s3 s4).markUpdate
            st0 id sid bk ans) =
        (⌜CliKpkInvFull rd F0 cliWrOk id sid bk m.2⌝ ∗
          dirAt A self m.2.oneTime ∗ dirAt A (self + 0x28#64) m.2.lastResort) := rfl
    have hout :
        kpkMarkPollOutAt (cliKpkStoreSpecFull A img.base rd F0 cliWrOk id sid bk s1 s2 s3 s4) out ans =
        unitSpePollOutAt (cliKpkMarkErrSpec A) out ans := rfl
    have hstk :
        (cliKpkStoreSpecFull A img.base rd F0 cliWrOk id sid bk s1 s2 s3 s4).markPollStack = s4 := rfl
    have hbox :
        (cliKpkStoreSpecFull A img.base rd F0 cliWrOk id sid bk s1 s2 s3 s4).markBoxAt
          fut self baseKeyA id sid 1#8 =
        kpkMarkBoxAt fut self baseKeyA id sid 1#8 := rfl
    rw [hstore, hout, hstk, hbox]
    have hgoal : sf.mem ⊨
        ⌜(cliKpkStoreSpecFull A img.base rd F0 cliWrOk id sid bk s1 s2 s3 s4).markRel
            st0 id sid bk ans ∧
          sf.trace = s0.trace ++ []⌝ ∗
        (⌜CliKpkInvFull rd F0 cliWrOk id sid bk m.2⌝ ∗
          (unitSpePollOutAt (cliKpkMarkErrSpec A) out ans ∗
            dirAt A self m.2.oneTime ∗ dirAt A (self + 0x28#64) m.2.lastResort ∗
            kpkMarkBoxAt fut self baseKeyA id sid 1#8 ∗
            (baseKeyA ↦ₛ bk.bytes.toList) ∗ A.pool ∗ stackAt s0.sp s4 ∗ R)) := by
      rw [satisfies_pure_sepConj]; refine ⟨⟨hrel, by rw [List.append_nil]; exact htr⟩, ?_⟩
      rw [satisfies_pure_sepConj]; exact ⟨hinv.mark, Eq.mp (congrArg (sf.mem ⊨ ·) (by ac_rfl)) hm'⟩
    exact Eq.mp (congrArg (sf.mem ⊨ ·) (by ac_rfl)) hgoal

theorem cliSignedPreKeyKitOk_of_hooksExt {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {F0 : FsFiles}
    {sid : BitVec 32} {readStk s1 s2 : Nat}
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooksExt img A ext)
    (hRead : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr Cli.readFileName)
      (readFileSpec cliIo.rd cliWrOk A img readStk))
    (hs1 : (cliKitStk ⟨readStk⟩).spkGetShim ≤ s1)
    (hs2 : (cliKitStk ⟨readStk⟩).spkGetPoll ≤ s2) :
    SignedPreKeyStoreKitOkImgE img
      (cliSignedPreKeyStoreSpec A img.base cliIo.rd F0 cliWrOk sid s1 s2) ext :=
  cliSpkKitOkImgE_of_hooksExt himg hh hRead
    (cliDecodeKyberPreKey_ok_of_alloc himg hh.alloc) hs1 hs2

theorem cliKyberKitOk_of_hooksExt {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {F0 : FsFiles}
    {kid ksid : BitVec 32} {kbk : PublicKey} {readStk s1 s2 s3 s4 : Nat}
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooksExt img A ext)
    (hRead : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr Cli.readFileName)
      (readFileSpec cliIo.rd cliWrOk A img readStk))
    (hs1 : (cliKitStk ⟨readStk⟩).kpkGetShim ≤ s1)
    (hs2 : (cliKitStk ⟨readStk⟩).kpkGetPoll ≤ s2)
    (hs3 : (cliKitStk ⟨readStk⟩).kpkMarkShim ≤ s3)
    (hs4 : (cliKitStk ⟨readStk⟩).kpkMarkPoll ≤ s4) :
    KyberPreKeyStoreKitOkImgE img
      (cliKpkStoreSpecFull A img.base cliIo.rd F0 cliWrOk kid ksid kbk s1 s2 s3 s4) ext :=
  cliKpkKitOkImgE_of_hooksExt himg hh hRead
    (cliDecodeKyberPreKey_ok_of_alloc himg hh.alloc) hs1 hs2 hs3 hs4

theorem cliPreKeyKitOk_of_hooksExt (C : Crypto) {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {F0 : FsFiles}
    {pid : BitVec 32} {readStk s1 s2 s3 s4 : Nat}
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooksExt img A ext)
    (hRead : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr Cli.readFileName)
      (readFileSpec cliIo.rd cliWrOk A img readStk))
    (hs1 : (cliKitStk ⟨readStk⟩).pkGetShim ≤ s1)
    (hs2 : (cliKitStk ⟨readStk⟩).pkGetPoll ≤ s2)
    (hs3 : (cliKitStk ⟨readStk⟩).pkRemoveShim ≤ s3)
    (hs4 : (cliKitStk ⟨readStk⟩).pkRemovePoll ≤ s4) :
    PreKeyStoreKitOkImgE img
      (cliPreKeyStoreSpec A img.base cliIo.rd F0 cliWrOk pid s1 s2 s3 s4) ext :=
  cliPkKitOkImgE_of_hooksExt himg hh hRead
    (cliPreKeyDeserialize_ok_of_alloc C himg hh.alloc) hs1 hs2 hs3 hs4

end ExtStoreKits

end CryptoVerification.SignalSession.Cli.RunProofs.Poll
