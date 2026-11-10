/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.StoreKit.Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.SelfKitOk
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable `[LibsignalPlacement]` CLI Self-Identity and Full Identity Store Kit

Defines `cliIdStoreSpecFullPlaced` and `cliIdSelfSpecFullPlaced` with `lsρ cliIdentityVtSym` vtable
addresses and proves quietness.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.Poll

open Arm64 Arm64.Process ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.StoreKit.IdentitySelf
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (FdsGe3Closed)
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate
open CryptoVerification.SignalSession.Cli.KitInst
open CryptoVerification.SignalSession.Cli.KitInst.SelfRel

/-- Relocatable `[LibsignalPlacement]` `cliIdStoreSpecFull` with `id_vt := lsρ cliIdentityVtSym`
and placed shim/future-vtable/poll/drop addresses. -/
def cliIdStoreSpecFullPlaced [LibsignalPlacement] (A : RustAlloc) (rd : ReadRule) (F0 : FsFiles)
    (pathOk : List (BitVec 8) → Prop) (peer : AddrGhost)
    (trustShimStk trustPollStk saveShimStk savePollStk : Nat) : IdentityStoreSpec A 0#64 :=
  { cliIdStoreSpecFull A 0#64 rd F0 pathOk peer
      trustShimStk trustPollStk saveShimStk savePollStk with
    id_vt := lsρ cliIdentityVtSym
    trustShimOff := lsmpl.base 601
    trustFutVtOff := lsρ idTrustFutVtSym
    trustPollOff := lsmpl.base 566
    trustFutDropOff := lsDropOffPlaced
    saveShimOff := lsmpl.base 600
    saveFutVtOff := lsρ idSaveFutVtSym
    savePollOff := lsmpl.base 565
    saveFutDropOff := lsDropOffPlaced
    trustFutDrop_ne_zero := fun _ => lsDropOffPlaced_ne_zero
    saveFutDrop_ne_zero := fun _ => lsDropOffPlaced_ne_zero }

/-- Relocatable `[LibsignalPlacement]` `IdentitySelfStoreSpec` over `cliIdStoreSpecFullPlaced`. -/
def cliIdSelfSpecFullPlaced [LibsignalPlacement] (A : RustAlloc) (rd : ReadRule) (F0 : FsFiles)
    (pathOk : List (BitVec 8) → Prop) (peer : AddrGhost)
    {t1 t2 t3 t4 : Nat}
    (kpShimStk kpPollStk regIdShimStk regIdPollStk : Nat) :
    IdentitySelfStoreSpec (cliIdStoreSpecFullPlaced A rd F0 pathOk peer t1 t2 t3 t4) where
  fdsOk := fun fs => FdsGe3Closed fs
  KpErr := CliSelfSpeErr
  RegIdErr := CliSelfSpeErr
  kpErr := cliSelfSpeErrSpec A
  regIdErr := cliSelfSpeErrSpec A
  kpRel := cliKpRel rd F0
  regIdRel := cliRegIdRel rd F0
  kpEvs := fun _ => []
  regIdEvs := fun _ => []
  kpShimOff := lsmpl.base 602
  kpFutVtOff := lsρ idKeyPairFutVtSym
  kpPollOff := lsmpl.base 567
  kpFutDropOff := lsDropOffPlaced
  regIdShimOff := lsmpl.base 603
  regIdFutVtOff := lsρ idRegIdFutVtSym
  regIdPollOff := lsmpl.base 568
  regIdFutDropOff := lsDropOffPlaced
  kpBoxSize := 16
  regIdBoxSize := 16
  kpShimStack := kpShimStk
  kpPollStack := kpPollStk
  regIdShimStack := regIdShimStk
  regIdPollStack := regIdPollStk
  kpBoxAt := idOwnFutBoxAt
  regIdBoxAt := idOwnFutBoxAt
  kpBoxAt_memRegion := idOwnFutBoxAt_memRegion
  regIdBoxAt_memRegion := idOwnFutBoxAt_memRegion
  kpBoxSize_ne_zero := by decide
  regIdBoxSize_ne_zero := by decide
  kpBoxSize_lt := by decide
  regIdBoxSize_lt := by decide
  kpFutDrop_ne_zero := fun _ => lsDropOffPlaced_ne_zero
  regIdFutDrop_ne_zero := fun _ => lsDropOffPlaced_ne_zero

theorem cliIdStoreSpecFullPlaced_quiet [LibsignalPlacement] {A : RustAlloc}
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop} {peer : AddrGhost}
    {t1 t2 t3 t4 : Nat} :
    (cliIdStoreSpecFullPlaced A rd F0 pathOk peer t1 t2 t3 t4).Quiet :=
  ⟨fun _ _ _ _ => by simp [cliIdStoreSpecFullPlaced, cliIdStoreSpecFull, cliIdentityStoreSpec, NoFsEv],
    fun _ _ _ => by simp [cliIdStoreSpecFullPlaced, cliIdStoreSpecFull, cliIdentityStoreSpec, NoFsEv]⟩

theorem cliIdSelfSpecFullPlaced_quiet [LibsignalPlacement] {A : RustAlloc}
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop} {peer : AddrGhost}
    {t1 t2 t3 t4 k1 k2 k3 k4 : Nat} :
    (cliIdSelfSpecFullPlaced A rd F0 pathOk peer (t1 := t1) (t2 := t2) (t3 := t3) (t4 := t4)
      k1 k2 k3 k4).Quiet :=
  ⟨fun _ => by simp [cliIdSelfSpecFullPlaced, NoFsEv],
    fun _ => by simp [cliIdSelfSpecFullPlaced, NoFsEv]⟩

theorem cliIdSelfSpecFullPlaced_kpRel_total [LibsignalPlacement] {A : RustAlloc}
    {peer : AddrGhost} {t1 t2 t3 t4 k1 k2 k3 k4 : Nat} (F0 : FsFiles) (g : IdGhost) :
    ∃ ans,
      (cliIdSelfSpecFullPlaced A cliIo.rd F0 cliWrOk peer
        (t1 := t1) (t2 := t2) (t3 := t3) (t4 := t4) k1 k2 k3 k4).kpRel g ans :=
  cliKpRel_total cliSelfSpeErrWitness cliIo.rd F0 g

theorem cliIdSelfSpecFullPlaced_regIdRel_total [LibsignalPlacement] {A : RustAlloc}
    {peer : AddrGhost} {t1 t2 t3 t4 k1 k2 k3 k4 : Nat} (F0 : FsFiles) (g : IdGhost) :
    ∃ ans,
      (cliIdSelfSpecFullPlaced A cliIo.rd F0 cliWrOk peer
        (t1 := t1) (t2 := t2) (t3 := t3) (t4 := t4) k1 k2 k3 k4).regIdRel g ans :=
  cliRegIdRel_total cliSelfSpeErrWitness cliIo.rd F0 g

end CryptoVerification.SignalSession.Cli.RunProofs.Poll
