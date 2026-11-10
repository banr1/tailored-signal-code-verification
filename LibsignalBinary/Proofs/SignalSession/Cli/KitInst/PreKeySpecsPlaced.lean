/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.PreKeySpecs
public import LibsignalBinary.Proofs.PublicApi.StoreKit.Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Placed CLI Pre-Key, Signed Pre-Key, and Kyber Store Specifications

Relocatable `[LibsignalPlacement]` instantiations of `cliPreKeyStoreSpec`,
`cliSignedPreKeyStoreSpec`, and `cliKyberPreKeyStoreSpec` at base `0#64`.
-/

@[expose] public section
set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.KitInst

open Arm64 Arm64.Obj ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.SignalSession
open CryptoVerification.SignalSession.Cli

/-- Relocatable `PreKeyStoreSpec` for `OneTimePreKeyFiles` at base `0#64`. -/
abbrev cliPreKeyStoreSpecPlaced [LibsignalPlacement] (A : RustAlloc) (rd : ReadRule) (F0 : FsFiles)
    (pathOk : List (BitVec 8) → Prop) (pid : BitVec 32)
    (getShimStk getPollStk removeShimStk removePollStk : Nat) : PreKeyStoreSpec A 0#64 :=
  { cliPreKeyStoreSpec A 0#64 rd F0 pathOk pid
      getShimStk getPollStk removeShimStk removePollStk with
    pk_vt := lsρ cliPreKeyVtSym
    getShimOff := lsmpl.base 608
    getFutVtOff := lsρ pkGetFutVtSym
    getPollOff := lsmpl.base 573
    getFutDropOff := lsDropOffPlaced
    removeShimOff := lsmpl.base 610
    removeFutVtOff := lsρ pkRemoveFutVtSym
    removePollOff := lsmpl.base 575
    removeFutDropOff := lsDropOffPlaced
    getFutDrop_ne_zero := fun _ => lsDropOffPlaced_ne_zero
    removeFutDrop_ne_zero := fun _ => lsDropOffPlaced_ne_zero }

/-- Relocatable `SignedPreKeyStoreSpec` for `SignedPreKeyFiles` at base `0#64`. -/
abbrev cliSignedPreKeyStoreSpecPlaced [LibsignalPlacement] (A : RustAlloc) (rd : ReadRule) (F0 : FsFiles)
    (pathOk : List (BitVec 8) → Prop) (sid : BitVec 32)
    (getShimStk getPollStk : Nat) : SignedPreKeyStoreSpec A 0#64 :=
  { cliSignedPreKeyStoreSpec A 0#64 rd F0 pathOk sid getShimStk getPollStk with
    spk_vt := lsρ cliSignedPreKeyVtSym
    getShimOff := lsmpl.base 606
    getFutVtOff := lsρ spkGetFutVtSym
    getPollOff := lsmpl.base 571
    getFutDropOff := lsDropOffPlaced
    getFutDrop_ne_zero := fun _ => lsDropOffPlaced_ne_zero }

/-- Relocatable `KyberPreKeyStoreSpec` for `KyberPreKeyFiles` at base `0#64`. -/
abbrev cliKyberPreKeyStoreSpecPlaced [LibsignalPlacement] (A : RustAlloc) (rd : ReadRule) (F0 : FsFiles)
    (pathOk : List (BitVec 8) → Prop) (kid ksid : BitVec 32) (kbk : PublicKey)
    (getShimStk getPollStk markShimStk markPollStk : Nat) : KyberPreKeyStoreSpec A 0#64 :=
  { cliKyberPreKeyStoreSpec A 0#64 rd F0 pathOk kid ksid kbk
      getShimStk getPollStk markShimStk markPollStk with
    kpk_vt := lsρ cliKyberPreKeyVtSym
    getShimOff := lsmpl.base 611
    getFutVtOff := lsρ kpkGetFutVtSym
    getPollOff := lsmpl.base 576
    getFutDropOff := lsDropOffPlaced
    markShimOff := lsmpl.base 613
    markFutVtOff := lsρ kpkMarkFutVtSym
    markPollOff := lsmpl.base 578
    markFutDropOff := lsDropOffPlaced
    getFutDrop_ne_zero := fun _ => lsDropOffPlaced_ne_zero
    markFutDrop_ne_zero := fun _ => lsDropOffPlaced_ne_zero }

theorem cliPreKeyStoreSpecPlaced_quiet [LibsignalPlacement] {A : RustAlloc}
    (rd : ReadRule) (F0 : FsFiles) (pathOk : List (BitVec 8) → Prop)
    (pid : BitVec 32) (s1 s2 s3 s4 : Nat) :
    (cliPreKeyStoreSpecPlaced A rd F0 pathOk pid s1 s2 s3 s4).Quiet :=
  cliPreKeyStoreSpec_quiet (A := A) (b := 0#64) rd F0 pathOk pid s1 s2 s3 s4

theorem cliSignedPreKeyStoreSpecPlaced_quiet [LibsignalPlacement] {A : RustAlloc}
    (rd : ReadRule) (F0 : FsFiles) (pathOk : List (BitVec 8) → Prop)
    (sid : BitVec 32) (s1 s2 : Nat) :
    (cliSignedPreKeyStoreSpecPlaced A rd F0 pathOk sid s1 s2).Quiet :=
  cliSignedPreKeyStoreSpec_quiet (A := A) (b := 0#64) rd F0 pathOk sid s1 s2

theorem cliKyberPreKeyStoreSpecPlaced_quiet [LibsignalPlacement] {A : RustAlloc}
    (rd : ReadRule) (F0 : FsFiles) (pathOk : List (BitVec 8) → Prop)
    (kid ksid : BitVec 32) (kbk : PublicKey) (s1 s2 s3 s4 : Nat) :
    (cliKyberPreKeyStoreSpecPlaced A rd F0 pathOk kid ksid kbk s1 s2 s3 s4).Quiet :=
  cliKpkStoreSpec_quiet (A := A) (b := 0#64) rd F0 pathOk kid ksid kbk
    (cliKpkGetSide A rd F0 pathOk kid) s1 s2 s3 s4 pkBoxAt_memRegion kpkMarkBoxAt_memRegion

theorem pkGetAnsAt_entails_pollOut_placed [LibsignalPlacement] (A : RustAlloc)
    (rd : ReadRule) (F0 : FsFiles) (pathOk : List (BitVec 8) → Prop) (pid : BitVec 32)
    (s1 s2 s3 s4 : Nat) (d : DirGhost) (id : BitVec 32) (out : BitVec 64) :
    let kit := cliPreKeyStoreSpecPlaced A rd F0 pathOk pid s1 s2 s3 s4
    let pa := pkAnsOf PreKeyRecord.deserialize (d.get rd F0 (keyName id))
    pkGetAnsAt A out pa ⊢
      ∃∗ ans : Except kit.GetErr PreKeyRecord,
        ⌜kit.getRel d id ans⌝ ∗ preKeyGetPollOutAt kit out ans := by
  intro kit pa
  have hout : preKeyGetPollOutAt kit out =
      preKeyGetPollOutAt (cliPreKeyStoreSpec A 0#64 rd F0 pathOk pid s1 s2 s3 s4) out := by
    funext ans; cases ans <;> rfl
  rw [hout]
  exact pkGetAnsAt_entails_pollOut A 0#64 rd F0 pathOk pid s1 s2 s3 s4 d id out

theorem pkRemoveOutAt_entails_pollOut_placed [LibsignalPlacement] (A : RustAlloc)
    (rd : ReadRule) (F0 : FsFiles) (pathOk : List (BitVec 8) → Prop) (pid : BitVec 32)
    (s1 s2 s3 s4 : Nat) (d : DirGhost) (id : BitVec 32) (out : BitVec 64) :
    let kit := cliPreKeyStoreSpecPlaced A rd F0 pathOk pid s1 s2 s3 s4
    let res := pkRemoveOf d (keyName id) (d.get rd F0 (keyName id))
    pkRemoveOutAt A out res.1 ⊢
      ∃∗ ans : Except kit.RemoveErr Unit,
        ⌜kit.removeRel d id ans ∧ res.2 = kit.removeUpdate d id ans⌝ ∗
        preKeyRemovePollOutAt kit out ans := by
  intro kit res
  have hout : preKeyRemovePollOutAt kit out =
      preKeyRemovePollOutAt (cliPreKeyStoreSpec A 0#64 rd F0 pathOk pid s1 s2 s3 s4) out := by
    funext ans; cases ans <;> rfl
  rw [hout]
  exact pkRemoveOutAt_entails_pollOut A 0#64 rd F0 pathOk pid s1 s2 s3 s4 d id out

theorem spkAnsAt_entails_pollOut_placed [LibsignalPlacement] (A : RustAlloc)
    (rd : ReadRule) (F0 : FsFiles) (pathOk : List (BitVec 8) → Prop) (sid : BitVec 32)
    (s1 s2 : Nat) (d : DirGhost) (id : BitVec 32) (out : BitVec 64) :
    let kit := cliSignedPreKeyStoreSpecPlaced A rd F0 pathOk sid s1 s2
    let pa := pkAnsOf SignedPreKeyRecord.deserialize (d.get rd F0 (keyName id))
    spkAnsAt A out pa ⊢
      ∃∗ ans : Except kit.GetErr SignedPreKeyRecord,
        ⌜kit.getRel d id ans⌝ ∗ spkGetPollOutAt kit out ans := by
  intro kit pa
  have hout : spkGetPollOutAt kit out =
      spkGetPollOutAt (cliSignedPreKeyStoreSpec A 0#64 rd F0 pathOk sid s1 s2) out := by
    funext ans; cases ans <;> rfl
  rw [hout]
  exact spkAnsAt_entails_pollOut A 0#64 rd F0 pathOk sid s1 s2 d id out

theorem kpkAnsAt_entails_pollOut_placed [LibsignalPlacement] (A : RustAlloc)
    (rd : ReadRule) (F0 : FsFiles) (pathOk : List (BitVec 8) → Prop)
    (kid ksid : BitVec 32) (kbk : PublicKey) (s1 s2 s3 s4 : Nat)
    (g : KyberGhost) (id : BitVec 32) (out : BitVec 64) :
    let kit := cliKyberPreKeyStoreSpecPlaced A rd F0 pathOk kid ksid kbk s1 s2 s3 s4
    let pa := kpkAnsOf
      (pkAnsOf KyberPreKeyRecord.deserialize (g.oneTime.get rd F0 (keyName id)))
      (pkAnsOf KyberPreKeyRecord.deserialize (g.lastResort.get rd F0 (keyName id)))
    kpkAnsAt A out pa ⊢
      ∃∗ ans : Except kit.GetErr KyberPreKeyRecord,
        ⌜kit.getRel g id ans⌝ ∗ kpkGetPollOutAt kit out ans := by
  intro kit pa
  have hout : kpkGetPollOutAt kit out =
      kpkGetPollOutAt (cliKpkStoreSpec A 0#64 rd F0 pathOk kid ksid kbk
        (cliKpkGetSide A rd F0 pathOk kid) s1 s2 s3 s4 pkBoxAt_memRegion kpkMarkBoxAt_memRegion) out := by
    funext ans; cases ans <;> rfl
  rw [hout]
  exact kpkAnsAt_entails_pollOut A 0#64 rd F0 pathOk kid ksid kbk s1 s2 s3 s4
    pkBoxAt_memRegion kpkMarkBoxAt_memRegion g id out

end CryptoVerification.SignalSession.Cli.KitInst
