/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Defs
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.StorePoll -- shake: keep
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityVtables
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.Shims
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.Existing
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.IkpTryFrom
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.IdKeyPairPoll
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.IdRegIdPoll
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.StorePollCli
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.Serialize
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.AddressText
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Decimal
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.GrowOneX
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Reserve11
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.SessionCloneAux.BasePart2
import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdSaveShim
import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdTrustShim
import LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPoll
import LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadShim
import LibsignalBinary.Proofs.SignalSession.Cli.Store.StoreShim

/-!
# CLI Store Vtable and Callback Contracts

Verifies all 13 CLI store vtable shims, polls, and future drops (`InitStoreCallees` on
`initProg img W` and `InitStoreCalleesExt` on `tripleRatchetProgAtExt img.base ext1`) at residual
stack `stk - cliInitiateFrame`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate

open Arm64 Arm64.Process ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.RecordCodecs
open CryptoVerification.E2E
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs

/-! ## PQ `IdentityFiles` Callback Symbol Names -/

abbrev idKeyPairShimName : String :=
  "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity_key_pair"

abbrev idKeyPairPollName : String :=
  "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity_key_pair::{closure#0}"

abbrev idRegIdShimName : String :=
  "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id"

abbrev idRegIdPollName : String :=
  "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id::{closure#0}"

theorem idKeyPairShim_fnOff :
    libsignalSessionCode.fnOff idKeyPairShimName =
      num% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity_key_pair") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl)
    (ls_lemma% fnOff "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity_key_pair")

theorem idKeyPairPoll_fnOff :
    libsignalSessionCode.fnOff idKeyPairPollName =
      num% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity_key_pair::{closure#0}") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl)
    (ls_lemma% fnOff "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity_key_pair::{closure#0}")

theorem idRegIdShim_fnOff :
    libsignalSessionCode.fnOff idRegIdShimName =
      num% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl)
    (ls_lemma% fnOff "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id")

theorem idRegIdPoll_fnOff :
    libsignalSessionCode.fnOff idRegIdPollName =
      num% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id::{closure#0}") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl)
    (ls_lemma% fnOff "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id::{closure#0}")

/-! ## Future Boxes and Specifications -/

abbrev idKeyPairFutVtOff : BitVec 64 :=
  bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity_key_pair::{closure#0}") - 0x18)

abbrev idRegIdFutVtOff : BitVec 64 :=
  bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id::{closure#0}") - 0x18)

/-- 16-byte future box allocated by `get_identity_key_pair` and `get_local_registration_id` shims:
`self` @0, `state` byte @8, 7 bytes uninitialized. -/
def idOwnFutBoxAt (box self : BitVec 64) (st : BitVec 8) : SepProp :=
  (box ↦₆₄ self) ∗ ((box + 8#64) ↦₈ st) ∗ memRegion (box + 9#64) 7

def idOwnShimSpec (futVtOff : BitVec 64) (A : RustAlloc) (img : Obj.Image)
    (stk : Nat) : Spec (BitVec 64) :=
  Spec.inImage
    { pre := fun self s =>
        ⌜s.readReg64 .x0 = self⌝ ∗ A.pool ∗ stackAt s.sp stk
      post := fun self s0 sf =>
        ⌜sf.readReg64 .x1 = img.base + futVtOff ∧ sf.readReg64 .x0 ≠ 0#64 ∧
          (sf.readReg64 .x0).toNat % 8 = 0 ∧ sf.trace = s0.trace⌝ ∗
          A.live (sf.readReg64 .x0) 16 8 ∗
          idOwnFutBoxAt (sf.readReg64 .x0) self 0#8 ∗
          A.pool ∗ stackAt s0.sp stk
      onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }
    img

structure IdOwnPollGhost where
  fut : BitVec 64
  out : BitVec 64
  self : BitVec 64
  own : DirGhost

/-- 72-byte sret of `get_identity_key_pair::{closure#0}`: the closure copies the 72-byte local
`Result<IdentityKeyPair, SignalProtocolError>` (laid out as `identityKeyPairResultAt` in
`Specifications/RecordCodecsBinary.lean`, which `<IdentityKeyPair as TryFrom<&[u8]>>::try_from` writes)
to `out`:
- `.ok kp`: tag byte `0`, the public key bytes @1, the private key bytes @0x21, 7 bytes unspecified.
- `.error ()`: tag byte `1`, 7 bytes unspecified, `RunDrop.SpeOwned` @8 (`InvalidState("read", _)`
  from `Dir::get`, or the error of `try_from`), 16 bytes unspecified. -/
def idKeyPairOutAt (A : RustAlloc) (out : BitVec 64) :
    Except Unit IdentityKeyPair → SepProp
  | .ok kp =>
    (out ↦₈ 0#8) ∗ ((out + 1#64) ↦ₛ kp.identityKey.publicKey.bytes.toList) ∗
      ((out + 0x21#64) ↦ₛ kp.privateKey.bytes.toList) ∗ memRegion (out + 0x41#64) 7
  | .error () =>
    (out ↦₈ 1#8) ∗ memRegion (out + 1#64) 7 ∗
      (∃∗ k : RunDrop.SpeOwned, RunDrop.speOwnedAt A (out + 8#64) k) ∗
      memRegion (out + 0x38#64) 16

def idKeyPairPollSpec (rd : ReadRule) (pathOk : List (BitVec 8) → Prop) (A : RustAlloc)
    (img : Obj.Image) (stk : Nat) : Spec IdOwnPollGhost :=
  Spec.inImage
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.fut ∧ s.readReg64 .x8 = x.out ∧
          x.own.path.length < 2 ^ 32 ∧
          pathOk (pathOf x.own.path (utf8 "identity-key-pair")) ∧
          ∀ bs, x.own.get rd s.fs.files (utf8 "identity-key-pair") = .ok bs →
            bs.length < 2 ^ 32⌝ ∗
          idOwnFutBoxAt x.fut x.self 0#8 ∗ dirAt A x.self x.own ∗
          memRegion x.out 72 ∗ logOff img ∗ A.pool ∗ stackAt s.sp stk
      post := fun x s0 sf =>
        (∃∗ ans : Except Unit IdentityKeyPair,
          ⌜ans = (IdGhost.mk x.own (.new [])).keyPair rd s0.fs.files ∧ sf.trace = s0.trace⌝ ∗
          idKeyPairOutAt A x.out ans) ∗
          idOwnFutBoxAt x.fut x.self 1#8 ∗ dirAt A x.self x.own ∗
          logOff img ∗ A.pool ∗ stackAt s0.sp stk
      onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }
    img

/-- 48-byte sret of `get_local_registration_id::{closure#0}`:
- `.ok reg`: word 0 `-2`, `u32` `reg` at `out + 8`, 36 bytes uninitialized.
- `.error ()`: `RunDrop.SpeOwned` at `out`: `InvalidState("read", _)` from `Dir::get`, or
  `InvalidState("registration-id", "malformed file")` when the file's length is not 4. -/
def idRegIdOutAt (A : RustAlloc) (out : BitVec 64) : Except Unit (BitVec 32) → SepProp
  | .ok reg =>
    (out ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗ ((out + 8#64) ↦₃₂ reg) ∗ memRegion (out + 12#64) 36
  | .error () => ∃∗ k : RunDrop.SpeOwned, RunDrop.speOwnedAt A out k

def idRegIdPollSpec (rd : ReadRule) (pathOk : List (BitVec 8) → Prop) (A : RustAlloc)
    (img : Obj.Image) (stk : Nat) : Spec IdOwnPollGhost :=
  Spec.inImage
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.fut ∧ s.readReg64 .x8 = x.out ∧
          x.own.path.length < 2 ^ 32 ∧
          pathOk (pathOf x.own.path (utf8 "registration-id"))⌝ ∗
          idOwnFutBoxAt x.fut x.self 0#8 ∗ dirAt A x.self x.own ∗
          memRegion x.out 48 ∗ A.pool ∗ stackAt s.sp stk
      post := fun x s0 sf =>
        (∃∗ ans : Except Unit (BitVec 32),
          ⌜ans = (IdGhost.mk x.own (.new [])).regId rd s0.fs.files ∧ sf.trace = s0.trace⌝ ∗
          idRegIdOutAt A x.out ans) ∗
          idOwnFutBoxAt x.fut x.self 1#8 ∗ dirAt A x.self x.own ∗
          A.pool ∗ stackAt s0.sp stk
      onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }
    img

/-! ## Bundled CLI Store Contracts -/

structure InitStoreCallees (img : Obj.Image) (A : RustAlloc) (W : CliHooks)
    (B : RunBudgets) (stk : Nat) : Prop where
  futDrop : subroutine_ok (initProg img W)
    ((initProg img W).fnAddr KitInst.cliIdFutDropName) futDropSpec
  idTrustShim : subroutine_ok (initProg img W)
    ((initProg img W).fnAddr idTrustShimName)
    (idTrustShimSpec A img (stk - cliInitiateFrame))
  idTrustPoll : subroutine_ok (initProg img W)
    ((initProg img W).fnAddr idTrustPollName)
    (idTrustPollSpec cliIo.rd cliWrOk A img (stk - cliInitiateFrame))
  sessLoadShim : subroutine_ok (initProg img W)
    ((initProg img W).fnAddr sessLoadShimName)
    (sessLoadShimSpec A img (stk - cliInitiateFrame))
  sessLoadPoll : subroutine_ok (initProg img W)
    ((initProg img W).fnAddr sessLoadPollName)
    (sessLoadPollSpec cliIo.rd cliWrOk (fun _ => False) A img (stk - cliInitiateFrame))
  idKeyPairShim : subroutine_ok (initProg img W)
    ((initProg img W).fnAddr idKeyPairShimName)
    (idOwnShimSpec idKeyPairFutVtOff A img (stk - cliInitiateFrame))
  idKeyPairPoll : subroutine_ok (initProg img W)
    ((initProg img W).fnAddr idKeyPairPollName)
    (idKeyPairPollSpec cliIo.rd cliWrOk A img (stk - cliInitiateFrame))
  idRegIdShim : subroutine_ok (initProg img W)
    ((initProg img W).fnAddr idRegIdShimName)
    (idOwnShimSpec idRegIdFutVtOff A img (stk - cliInitiateFrame))
  idRegIdPoll : subroutine_ok (initProg img W)
    ((initProg img W).fnAddr idRegIdPollName)
    (idRegIdPollSpec cliIo.rd cliWrOk A img (stk - cliInitiateFrame))
  idSaveShim : subroutine_ok (initProg img W)
    ((initProg img W).fnAddr idSaveShimName)
    (idSaveShimSpec A img (stk - cliInitiateFrame))
  idSavePoll : subroutine_ok (initProg img W)
    ((initProg img W).fnAddr idSavePollName)
    (idSavePollSpec cliIo.rd cliWrOk A img (stk - cliInitiateFrame))
  sessStoreShim : subroutine_ok (initProg img W)
    ((initProg img W).fnAddr sessStoreShimName)
    (sessStoreShimSpec A img (stk - cliInitiateFrame))
  sessStorePoll : subroutine_ok (initProg img W)
    ((initProg img W).fnAddr sessStorePollName)
    (sessStorePollSpec A img (stk - cliInitiateFrame))

/-- All 12 CLI store functions and future drop hold at `stk - cliInitiateFrame` under `cliInitiateNeed B ≤ stk ≤ 2 ^ 63`. -/
theorem initStoreCallees_ok {img : Obj.Image} {A : RustAlloc} (W : CliHooks) (B : RunBudgets)
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooks img A (cliExterns W))
    (hRead : subroutine_ok (initProg img W)
      ((initProg img W).fnAddr Cli.readFileName)
      (readFileSpec cliIo.rd cliWrOk A img B.readFile))
    (stk : Nat) (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63) :
    InitStoreCallees img A W B stk := by
  have _ := hstk64
  have hGet := dirGet_cli_ok W B himg hh hRead
  have hBase := RunSkeleton.base_aligned himg
  have hShimStk : 32 + extHookStack ≤ stk - cliInitiateFrame := by
    have := stk_sub_ge_base hstk
    dsimp only [extHookStack]
    omega
  exact
    { futDrop := StoreCalleesProofs.futDrop_cli_ok img W
      idTrustShim := idTrustShim_cli_ok W B himg hh hstk
      idTrustPoll := idTrustPoll_cli_ok W B himg hh hRead hstk
      sessLoadShim := sessLoadShim_cli_ok W B himg hh hstk
      sessLoadPoll := sessLoadPoll_cli_ok W B himg hh hRead hstk
      idKeyPairShim := StoreCalleesProofs.idOwnShim_lift_stk
        (StoreCalleesProofs.idKeyPairShim_fixed_ok hh.alloc hBase) hShimStk
      idKeyPairPoll := subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp =>
        subroutine_ok.mono_outcome
          (IdKeyPairPoll.idKeyPairPoll_cli_ok W B himg hh hGet
            (identityKeyPairTryFrom_cli_ok W.C himg hh.alloc) hstk)
          ⟨x.fut, x.out, x.self, x.own⟩ R s0 hpc hrun hpre hsp fun _ hout => hout
      idRegIdShim := StoreCalleesProofs.idOwnShim_lift_stk
        (StoreCalleesProofs.idRegIdShim_fixed_ok hh.alloc hBase) hShimStk
      idRegIdPoll := subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp =>
        subroutine_ok.mono_outcome
          (IdRegIdPoll.idRegIdPoll_cli_ok W B himg hh hGet hstk)
          ⟨x.fut, x.out, x.self, x.own⟩ R s0 hpc hrun hpre hsp fun _ hout => hout
      idSaveShim := idSaveShim_cli_ok W B himg hh hstk
      idSavePoll := idSavePoll_cli_ok W B himg hh hRead hstk
      sessStoreShim := sessStoreShim_cli_ok W B himg hh hstk
      sessStorePoll := StorePollCli.sessStorePoll_cli_ok_of_ser W B himg hh
        (SerializeExt.serializeCanon_ok_x img A (cliExterns W) hh.alloc) hstk }

/-! ## Contract-Parameterized Store Callee Bundle (`InitStoreCalleesExt`) -/

section FutDropExt

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-- Future drop contract on `tripleRatchetProgAtExt img.base ext1`. -/
theorem futDrop_ext_ok (img : Obj.Image) (ext1 : String → Option (State → State)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext1)
      ((tripleRatchetProgAtExt img.base ext1).fnAddr KitInst.cliIdFutDropName) futDropSpec := by
  simp only [futDropSpec]
  have hfn : libsignalSessionCode.fnOff KitInst.cliIdFutDropName =
      num% (ls_off% "core::ptr::drop_glue::<<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity::{closure#0}>") :=
    KitInst.cliIdFutDrop_fnOff
  code_fetches CryptoVerification.libsignalSessionCode StoreCalleesProofs.cliInitFutDropBin img.base
    (Rust.withPanics ext1) hfn
    (num% (ls_off% "core::ptr::drop_glue::<<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity::{closure#0}>")) 4
  dsimp only [tripleRatchetProgAtExt] at ⊢
  clear hfn
  wp_init x s0
  examples_generalize_entry
  examples_hide_fetches
  wp_steps
  wp_done

end FutDropExt

/-- Hook and leaf dependencies for `InitStoreCalleesExt` on `tripleRatchetProgAtExt img.base ext1`. -/
structure StoreExtDeps (img : Obj.Image) (A : RustAlloc) (P : PEParams)
    (ext1 : String → Option (State → State)) (B : RunBudgets) (stk : Nat) : Prop where
  alloc : AllocContractsX img A ext1
  memcpyRO : HookSat ext1 memcpyName SpqrV1.Alloc.sessionMemcpyRegionROSpec
  bcmp : HookSat ext1 cliBcmpName cliBcmpSpec
  fs : TraceFsSound (tripleRatchetProgAtExt img.base ext1)
  dirGet : subroutine_ok (tripleRatchetProgAtExt img.base ext1)
    ((tripleRatchetProgAtExt img.base ext1).fnAddr dirGetName)
    (dirGetSpec cliIo.rd cliWrOk A img B.dirGetNeed)
  idTrustPoll : subroutine_ok (tripleRatchetProgAtExt img.base ext1)
    ((tripleRatchetProgAtExt img.base ext1).fnAddr idTrustPollName)
    (idTrustPollSpec cliIo.rd cliWrOk A img (stk - cliInitiateFrame))
  idSavePoll : subroutine_ok (tripleRatchetProgAtExt img.base ext1)
    ((tripleRatchetProgAtExt img.base ext1).fnAddr idSavePollName)
    (idSavePollSpec cliIo.rd cliWrOk A img (stk - cliInitiateFrame))

/-- `ext1`-parameterized `InitStoreCallees` bundle on `tripleRatchetProgAtExt img.base ext1`. -/
structure InitStoreCalleesExt (img : Obj.Image) (A : RustAlloc)
    (ext1 : String → Option (State → State)) (B : RunBudgets) (stk : Nat) : Prop where
  futDrop : subroutine_ok (tripleRatchetProgAtExt img.base ext1)
    ((tripleRatchetProgAtExt img.base ext1).fnAddr KitInst.cliIdFutDropName) futDropSpec
  idTrustShim : subroutine_ok (tripleRatchetProgAtExt img.base ext1)
    ((tripleRatchetProgAtExt img.base ext1).fnAddr idTrustShimName)
    (idTrustShimSpec A img (stk - cliInitiateFrame))
  idTrustPoll : subroutine_ok (tripleRatchetProgAtExt img.base ext1)
    ((tripleRatchetProgAtExt img.base ext1).fnAddr idTrustPollName)
    (idTrustPollSpec cliIo.rd cliWrOk A img (stk - cliInitiateFrame))
  sessLoadShim : subroutine_ok (tripleRatchetProgAtExt img.base ext1)
    ((tripleRatchetProgAtExt img.base ext1).fnAddr sessLoadShimName)
    (sessLoadShimSpec A img (stk - cliInitiateFrame))
  sessLoadPoll : subroutine_ok (tripleRatchetProgAtExt img.base ext1)
    ((tripleRatchetProgAtExt img.base ext1).fnAddr sessLoadPollName)
    (sessLoadPollSpec cliIo.rd cliWrOk (fun _ => False) A img (stk - cliInitiateFrame))
  idKeyPairShim : subroutine_ok (tripleRatchetProgAtExt img.base ext1)
    ((tripleRatchetProgAtExt img.base ext1).fnAddr idKeyPairShimName)
    (idOwnShimSpec idKeyPairFutVtOff A img (stk - cliInitiateFrame))
  idKeyPairPoll : subroutine_ok (tripleRatchetProgAtExt img.base ext1)
    ((tripleRatchetProgAtExt img.base ext1).fnAddr idKeyPairPollName)
    (idKeyPairPollSpec cliIo.rd cliWrOk A img (stk - cliInitiateFrame))
  idRegIdShim : subroutine_ok (tripleRatchetProgAtExt img.base ext1)
    ((tripleRatchetProgAtExt img.base ext1).fnAddr idRegIdShimName)
    (idOwnShimSpec idRegIdFutVtOff A img (stk - cliInitiateFrame))
  idRegIdPoll : subroutine_ok (tripleRatchetProgAtExt img.base ext1)
    ((tripleRatchetProgAtExt img.base ext1).fnAddr idRegIdPollName)
    (idRegIdPollSpec cliIo.rd cliWrOk A img (stk - cliInitiateFrame))
  idSaveShim : subroutine_ok (tripleRatchetProgAtExt img.base ext1)
    ((tripleRatchetProgAtExt img.base ext1).fnAddr idSaveShimName)
    (idSaveShimSpec A img (stk - cliInitiateFrame))
  idSavePoll : subroutine_ok (tripleRatchetProgAtExt img.base ext1)
    ((tripleRatchetProgAtExt img.base ext1).fnAddr idSavePollName)
    (idSavePollSpec cliIo.rd cliWrOk A img (stk - cliInitiateFrame))
  sessStoreShim : subroutine_ok (tripleRatchetProgAtExt img.base ext1)
    ((tripleRatchetProgAtExt img.base ext1).fnAddr sessStoreShimName)
    (sessStoreShimSpec A img (stk - cliInitiateFrame))
  sessStorePoll : subroutine_ok (tripleRatchetProgAtExt img.base ext1)
    ((tripleRatchetProgAtExt img.base ext1).fnAddr sessStorePollName)
    (sessStorePollSpec A img (stk - cliInitiateFrame))

/-- All 13 CLI store callees hold at `stk - cliInitiateFrame` under `StoreExtDeps`. -/
theorem initStoreCallees_ext_ok {img : Obj.Image} {A : RustAlloc} {P : PEParams}
    {ext1 : String → Option (State → State)} (B : RunBudgets) {stk : Nat}
    (himg : Obj.Loads libsignalSessionImage img)
    (hd : StoreExtDeps img A P ext1 B stk)
    (hstk : cliInitiateNeed B ≤ stk) (_hstk64 : stk ≤ 2 ^ 63) :
    InitStoreCalleesExt img A ext1 B stk := by
  have hb := RunSkeleton.base_aligned himg
  have h1 := stk_sub_ge_base hstk
  have h2 := stk_sub_ge_dirGet hstk
  have hRes := cliDoReserve_ok hd.alloc (Nat.le_refl doReserveStackX)
  have hDec := Decimal.decimal_ok_of_deps hRes (Nat.le_refl (10 * 80 + doReserveStackX)) hb
  have hAddrText : subroutine_ok (tripleRatchetProgAtExt img.base ext1)
      ((tripleRatchetProgAtExt img.base ext1).fnAddr addressTextName)
      (addrTextSpec A img cliAddrTextStk) :=
    AddressText.addressText_ok_of_deps hd.alloc hRes hDec (Nat.le_refl _) hb
  have hGrow := GrowOne.growOneDir_ok_x hd.alloc (Nat.le_refl (64 + finishGrowStackX)) hb
  have hDirPut : subroutine_ok (tripleRatchetProgAtExt img.base ext1)
      ((tripleRatchetProgAtExt img.base ext1).fnAddr dirPutName)
      (dirPutSpec A img cliDirPutStk) :=
    Put.dirPut_ok_of_deps hd.alloc hd.bcmp hGrow (Nat.le_refl _) hb
  have hShimStk : 32 + extHookStack ≤ stk - cliInitiateFrame := by
    dsimp only [extHookStack]; omega
  have hShim48 : 48 + extHookStack ≤ 516880 := by
    dsimp only [extHookStack]; decide
  have hShim32 : 32 + extHookStack ≤ 516880 := by
    dsimp only [extHookStack]; decide
  have hKpBounds : smallRootStack ≤ 65536 ∧ extHookStack ≤ 65536 := by
    dsimp only [smallRootStack, extHookStack]; decide
  have hStoreBounds : 208 + max (max cliAddrTextStk SerializeExt.serializeStackX)
      (max cliDirPutStk extHookStack) ≤ 516880 := by decide
  exact
    { futDrop := futDrop_ext_ok img ext1
      idTrustShim := Store.IdTrustShim.idTrustShim_ok_of_deps hd.alloc (by omega) hb
      idTrustPoll := hd.idTrustPoll
      sessLoadShim := Store.LoadShim.sessLoadShim_ok_of_deps hd.alloc (by omega) hb
      sessLoadPoll := Store.LoadPoll.sessLoadPoll_ok_of_deps hd.alloc hAddrText hd.dirGet
        sessDeserialize_false_ok hd.fs (sessLoadPoll_stk_le (by decide) hstk) hb
      idKeyPairShim := StoreCalleesProofs.idOwnShim_lift_stk
        (StoreCalleesProofs.idKeyPairShim_fixed_ok hd.alloc hb) hShimStk
      idKeyPairPoll := subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp =>
        subroutine_ok.mono_outcome
          (IdKeyPairPoll.idKeyPairPoll_ok_of_deps himg hd.alloc hd.dirGet
            (identityKeyPairTryFrom_cli_ok P.C himg hd.alloc)
            (by dsimp only [IdKeyPairPoll.kpCalleeStk]; omega) hb)
          ⟨x.fut, x.out, x.self, x.own⟩ R s0 hpc hrun hpre hsp fun _ hout => hout
      idRegIdShim := StoreCalleesProofs.idOwnShim_lift_stk
        (StoreCalleesProofs.idRegIdShim_fixed_ok hd.alloc hb) hShimStk
      idRegIdPoll := subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp =>
        subroutine_ok.mono_outcome
          (IdRegIdPoll.idRegIdPoll_ok_of_deps himg hd.alloc hd.dirGet
            (by dsimp only [IdRegIdPoll.regCalleeStk]; omega) hb)
          ⟨x.fut, x.out, x.self, x.own⟩ R s0 hpc hrun hpre hsp fun _ hout => hout
      idSaveShim := Store.IdSaveShim.idSaveShim_ok_of_deps hd.alloc (by omega) hb
      idSavePoll := hd.idSavePoll
      sessStoreShim := Store.StoreShim.sessStoreShim_ok_of_deps hd.alloc (by omega) hb
      sessStorePoll := Cli.Store.StorePoll.Helpers.sessStorePoll_of_inner
        (fun hhi => StorePollCli.sessStorePollInner_ok_x hAddrText
          (SerializeExt.serializeCanon_ok_x img A ext1 hd.alloc) hDirPut hhi)
        (by omega) }

theorem initStoreCallees_of_ext {img : Obj.Image} {A : RustAlloc} {W : CliHooks}
    {B : RunBudgets} {stk : Nat}
    (h : InitStoreCalleesExt img A (cliExterns W) B stk) :
    InitStoreCallees img A W B stk :=
  { futDrop := h.futDrop
    idTrustShim := h.idTrustShim
    idTrustPoll := h.idTrustPoll
    sessLoadShim := h.sessLoadShim
    sessLoadPoll := h.sessLoadPoll
    idKeyPairShim := h.idKeyPairShim
    idKeyPairPoll := h.idKeyPairPoll
    idRegIdShim := h.idRegIdShim
    idRegIdPoll := h.idRegIdPoll
    idSaveShim := h.idSaveShim
    idSavePoll := h.idSavePoll
    sessStoreShim := h.sessStoreShim
    sessStorePoll := h.sessStorePoll }

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate
