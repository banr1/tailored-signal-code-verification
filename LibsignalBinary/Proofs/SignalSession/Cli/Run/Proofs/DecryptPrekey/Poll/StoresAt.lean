/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.KyberKitOk
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.SelfKitOk

/-!
# Spatial Store Bridge for `decrypt_prekey` Poll

Proves the bidirectional separation-logic bridge between `MainHops.storesAt A a g`
(eight `Dir` slots at `+0x00 .. +0x118`) and the spatial store predicates of the CLI
store kits together with the untouched `pub` directory at `a + 0x118#64`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.Poll

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.E2E
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.RecordCodecs
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.KitInst

private theorem add_0x78_0x28 (a : BitVec 64) : (a + 0x78#64) + 0x28#64 = a + 0xa0#64 := by
  rw [BitVec.add_assoc]; rfl

private theorem pure_sepConj_true {φ : Prop} (P : SepProp) (hφ : φ) : ⌜φ⌝ ∗ P = P := by
  have hEq : φ = True := propext ⟨fun _ => trivial, fun _ => hφ⟩
  rw [hEq, pure_true, emp_sepConj]

/-- Session store kit for one `decrypt_prekey` poll on `F0` and `peer`. -/
def cliPollSessKit (A : RustAlloc) (b : BitVec 64) (F0 : FsFiles)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (peer : AddrGhost) (σ : DpKitStk) :
    SessionStoreSpec A b :=
  cliSessionStoreSpec A b cliIo.rd F0 cliWrOk Scope peer
    σ.sessLoadShim σ.sessLoadPoll σ.sessStoreShim σ.sessStorePoll

def cliPollIdKit (A : RustAlloc) (b : BitVec 64) (F0 : FsFiles)
    (peer : AddrGhost) (σ : DpKitStk) : IdentityStoreSpec A b :=
  cliIdStoreSpecFull A b cliIo.rd F0 cliWrOk peer
    σ.idTrustShim σ.idTrustPoll σ.idSaveShim σ.idSavePoll

def cliPollSelfKit (A : RustAlloc) (b : BitVec 64) (F0 : FsFiles)
    (peer : AddrGhost) (σ : DpKitStk) :
    IdentitySelf.IdentitySelfStoreSpec (cliPollIdKit A b F0 peer σ) :=
  cliIdSelfSpecFull A b cliIo.rd F0 cliWrOk peer
    σ.kpShim σ.kpPoll σ.regIdShim σ.regIdPoll

def cliPollPkKit (A : RustAlloc) (b : BitVec 64) (F0 : FsFiles)
    (pid : BitVec 32) (σ : DpKitStk) : PreKeyStoreSpec A b :=
  cliPreKeyStoreSpec A b cliIo.rd F0 cliWrOk pid
    σ.pkGetShim σ.pkGetPoll σ.pkRemoveShim σ.pkRemovePoll

def cliPollSpkKit (A : RustAlloc) (b : BitVec 64) (F0 : FsFiles)
    (sid : BitVec 32) (σ : DpKitStk) : SignedPreKeyStoreSpec A b :=
  cliSignedPreKeyStoreSpec A b cliIo.rd F0 cliWrOk sid
    σ.spkGetShim σ.spkGetPoll

def cliPollKpkKit (A : RustAlloc) (b : BitVec 64) (F0 : FsFiles)
    (kid ksid : BitVec 32) (kbk : PublicKey) (σ : DpKitStk) : KyberPreKeyStoreSpec A b :=
  cliKpkStoreSpecFull A b cliIo.rd F0 cliWrOk kid ksid kbk
    σ.kpkGetShim σ.kpkGetPoll σ.kpkMarkShim σ.kpkMarkPoll

/-- Separating conjunction of the CLI store kits' spatial predicates and the untouched
`pub` directory at `a + 0x118#64`. -/
def cliPollStoresKitsAt (A : RustAlloc) (b : BitVec 64) (F0 : FsFiles)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (peer : AddrGhost)
    (pid sid kid : BitVec 32) (kbk : PublicKey) (σ : DpKitStk)
    (a : BitVec 64) (g : StoresGhost) : SepProp :=
  (cliPollSessKit A b F0 Scope peer σ).storeAt (a + 0xf0#64) g.sessions ∗
    (cliPollIdKit A b F0 peer σ).identityAt a g.identity ∗
    (cliPollPkKit A b F0 pid σ).storeAt (a + 0xc8#64) g.oneTime ∗
    (cliPollSpkKit A b F0 sid σ).storeAt (a + 0x50#64) g.signed ∗
    (cliPollKpkKit A b F0 kid sid kbk σ).storeAt (a + 0x78#64) g.kyber ∗
    dirAt A (a + 0x118#64) g.pub

/-- Unpacks `storesAt A a g` under the pure store invariants into `cliPollStoresKitsAt`
at the directory offsets passed in `dpSlotArgs`. -/
theorem storesAt_entails_cliPollStoresKitsAt
    {A : RustAlloc} (b : BitVec 64) {F0 : FsFiles}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {peer : AddrGhost}
    {pid sid kid : BitVec 32} {kbk : PublicKey} (σ : DpKitStk)
    (a : BitVec 64) (g : StoresGhost)
    (hSess : CliSessInv cliIo.rd F0 cliWrOk Scope peer g.sessions)
    (hIdOwn : CliIdOwnInv cliIo.rd F0 cliWrOk g.identity.own)
    (hId : CliIdInv cliIo.rd F0 cliWrOk peer g.identity)
    (hPk : CliPkInv cliIo.rd F0 cliWrOk pid g.oneTime)
    (hSpk : CliSpkInv cliIo.rd F0 cliWrOk sid g.signed)
    (hKpk : CliKpkInvFull cliIo.rd F0 cliWrOk kid sid kbk g.kyber) :
    storesAt A a g ⊢
      cliPollStoresKitsAt A b F0 Scope peer pid sid kid kbk σ a g := by
  unfold storesAt cliPollStoresKitsAt
  dsimp only [cliPollSessKit, cliPollIdKit, cliPollPkKit, cliPollSpkKit, cliPollKpkKit,
    cliSessionStoreSpec, cliIdStoreSpecFull, cliPreKeyStoreSpec, cliSignedPreKeyStoreSpec,
    cliKpkStoreSpecFull, cliSessStoreAt, cliIdStoreAtFull, cliIdStoreAt, cliPkStoreAt,
    cliSpkStoreAt, cliKpkStoreAtFull]
  rw [add_0x78_0x28 a]
  rw [pure_sepConj_true _ hSess, pure_sepConj_true _ hIdOwn, pure_sepConj_true _ hId,
      pure_sepConj_true _ hPk, pure_sepConj_true _ hSpk, pure_sepConj_true _ hKpk]
  exact Entails.of_eq (by ac_rfl)

/-- Repacks `cliPollStoresKitsAt` at an updated ghost state `g'` back into `storesAt A a g'`. -/
theorem cliPollStoresKitsAt_entails_storesAt
    {A : RustAlloc} (b : BitVec 64) {F0 : FsFiles}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {peer : AddrGhost}
    {pid sid kid : BitVec 32} {kbk : PublicKey} (σ : DpKitStk)
    (a : BitVec 64) (g' : StoresGhost) :
    cliPollStoresKitsAt A b F0 Scope peer pid sid kid kbk σ a g' ⊢
      storesAt A a g' := by
  unfold cliPollStoresKitsAt storesAt
  dsimp only [cliPollSessKit, cliPollIdKit, cliPollPkKit, cliPollSpkKit, cliPollKpkKit,
    cliSessionStoreSpec, cliIdStoreSpecFull, cliPreKeyStoreSpec, cliSignedPreKeyStoreSpec,
    cliKpkStoreSpecFull, cliSessStoreAt, cliIdStoreAtFull, cliIdStoreAt, cliPkStoreAt,
    cliSpkStoreAt, cliKpkStoreAtFull]
  rw [add_0x78_0x28 a]
  have drop1 (P : Prop) (Q : SepProp) : ⌜P⌝ ∗ Q ⊢ Q := Entails.pure_left fun _ => Entails.refl _
  have drop2 (P1 P2 : Prop) (Q : SepProp) : ⌜P1⌝ ∗ (⌜P2⌝ ∗ Q) ⊢ Q :=
    Entails.pure_left fun _ => drop1 P2 Q
  refine Entails.trans
    (sepConj_mono (drop1 _ _)
      (sepConj_mono (drop2 _ _ _)
        (sepConj_mono (drop1 _ _)
          (sepConj_mono (drop1 _ _)
            (sepConj_mono (drop1 _ _) (Entails.refl _)))))) ?_
  exact Entails.of_eq (by ac_rfl)

end CryptoVerification.SignalSession.Cli.RunProofs.Poll
