/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StoresAt
public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.KitCodecsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureDefsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.KitRelDet
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionVtablesPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityVtablesPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.PreKeyVtablesPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdKeyPairVtablesPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdRegIdVtablesPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Placed
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4None
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.InitInv

/-!
# Relocatable `[LibsignalPlacement]` CLI Store Kits and Vtable/Quietness Helpers

Defines the six `[LibsignalPlacement]` CLI poll store kits (`cliPoll*KitPlaced` and
`cliPollStoresKitsAtPlaced`) and proves quietness, `loadRec` determinism, `FsAt`, and placed vtable
bundles (`stageP1VtablesPlacedAt`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.Poll

open Arm64 ProofLib
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.KitInst
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (CliGhostHooks cliGhostExterns)

noncomputable abbrev dpPollProgPlaced [LibsignalPlacement] (ext : String → Option (State → State)) : Program :=
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits.stageP1ProgPlaced ext

noncomputable abbrev dpPollEntryPlaced [LibsignalPlacement] : BitVec 64 :=
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits.stageP1EntryPlaced

/-! ## 1. Placed 6-Kit Bundle (`cliPoll*KitPlaced`) & `storesAt` Bridge -/

def cliPollSessKitPlaced [LibsignalPlacement] (A : RustAlloc) (F0 : FsFiles)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (peer : AddrGhost) (σ : DpKitStk) :
    SessionStoreSpec A 0#64 :=
  { cliPollSessKit A 0#64 F0 Scope peer σ with
    ss_vt := lsρ cliSessionVtSym
    id_vt := lsρ cliIdentityVtSym
    loadShimOff := lsmpl.base 604
    storeShimOff := lsmpl.base 605
    loadFutVtOff := lsρ sessLoadFutVtSym
    storeFutVtOff := lsρ sessStoreFutVtSym
    loadPollOff := lsmpl.base 569
    storePollOff := lsmpl.base 570
    loadFutDropOff := lsDropOffPlaced
    storeFutDropOff := lsDropOffPlaced
    loadFutDrop_ne_zero := fun _ => lsDropOffPlaced_ne_zero
    storeFutDrop_ne_zero := fun _ => lsDropOffPlaced_ne_zero }

def cliPollIdKitPlaced [LibsignalPlacement] (A : RustAlloc) (F0 : FsFiles)
    (peer : AddrGhost) (σ : DpKitStk) : IdentityStoreSpec A 0#64 :=
  cliIdStoreSpecFullPlaced A cliIo.rd F0 cliWrOk peer
    σ.idTrustShim σ.idTrustPoll σ.idSaveShim σ.idSavePoll

def cliPollSelfKitPlaced [LibsignalPlacement] (A : RustAlloc) (F0 : FsFiles)
    (peer : AddrGhost) (σ : DpKitStk) :
    IdentitySelf.IdentitySelfStoreSpec (cliPollIdKitPlaced A F0 peer σ) :=
  cliIdSelfSpecFullPlaced A cliIo.rd F0 cliWrOk peer
    σ.kpShim σ.kpPoll σ.regIdShim σ.regIdPoll

def cliPollPkKitPlaced [LibsignalPlacement] (A : RustAlloc) (F0 : FsFiles)
    (pid : BitVec 32) (σ : DpKitStk) : PreKeyStoreSpec A 0#64 :=
  cliPreKeyStoreSpecPlaced A cliIo.rd F0 cliWrOk pid
    σ.pkGetShim σ.pkGetPoll σ.pkRemoveShim σ.pkRemovePoll

def cliPollSpkKitPlaced [LibsignalPlacement] (A : RustAlloc) (F0 : FsFiles)
    (sid : BitVec 32) (σ : DpKitStk) : SignedPreKeyStoreSpec A 0#64 :=
  cliSignedPreKeyStoreSpecPlaced A cliIo.rd F0 cliWrOk sid
    σ.spkGetShim σ.spkGetPoll

def cliPollKpkKitPlaced [LibsignalPlacement] (A : RustAlloc) (F0 : FsFiles)
    (kid ksid : BitVec 32) (kbk : PublicKey) (σ : DpKitStk) : KyberPreKeyStoreSpec A 0#64 :=
  cliKpkStoreSpecFullPlaced A cliIo.rd F0 cliWrOk kid ksid kbk
    σ.kpkGetShim σ.kpkGetPoll σ.kpkMarkShim σ.kpkMarkPoll

/-- The separating conjunction of all 5 placed CLI store kits' spatial predicates plus the untouched
`pub` directory at `a + 0x118#64` (definitionally equal to `cliPollStoresKitsAt A 0#64...`). -/
def cliPollStoresKitsAtPlaced [LibsignalPlacement] (A : RustAlloc) (F0 : FsFiles)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (peer : AddrGhost)
    (pid sid kid : BitVec 32) (kbk : PublicKey) (σ : DpKitStk)
    (a : BitVec 64) (g : StoresGhost) : SepProp :=
  (cliPollSessKitPlaced A F0 Scope peer σ).storeAt (a + 0xf0#64) g.sessions ∗
    (cliPollIdKitPlaced A F0 peer σ).identityAt a g.identity ∗
    (cliPollPkKitPlaced A F0 pid σ).storeAt (a + 0xc8#64) g.oneTime ∗
    (cliPollSpkKitPlaced A F0 sid σ).storeAt (a + 0x50#64) g.signed ∗
    (cliPollKpkKitPlaced A F0 kid sid kbk σ).storeAt (a + 0x78#64) g.kyber ∗
    dirAt A (a + 0x118#64) g.pub

theorem storesAt_entails_cliPollStoresKitsAtPlaced [LibsignalPlacement]
    {A : RustAlloc} {F0 : FsFiles}
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
      cliPollStoresKitsAtPlaced A F0 Scope peer pid sid kid kbk σ a g :=
  storesAt_entails_cliPollStoresKitsAt 0#64 σ a g hSess hIdOwn hId hPk hSpk hKpk

theorem cliPollStoresKitsAtPlaced_entails_storesAt [LibsignalPlacement]
    {A : RustAlloc} {F0 : FsFiles}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {peer : AddrGhost}
    {pid sid kid : BitVec 32} {kbk : PublicKey} (σ : DpKitStk)
    (a : BitVec 64) (g' : StoresGhost) :
    cliPollStoresKitsAtPlaced A F0 Scope peer pid sid kid kbk σ a g' ⊢
      storesAt A a g' :=
  cliPollStoresKitsAt_entails_storesAt 0#64 σ a g'

/-! ## 2. Quietness, `loadRec` Determinism, and `FsAt` on `dpPollProgPlaced` -/

private theorem cliPollSess_quiet' {A : RustAlloc} (b : BitVec 64)
    (F0 : FsFiles) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (peer : AddrGhost) (σ : DpKitStk) :
    (cliPollSessKit A b F0 Scope peer σ).Quiet :=
  ⟨fun _ _ _ => NoFsEv.nil, fun _ _ _ _ => NoFsEv.nil⟩

theorem cliPollSessPlaced_quiet [LibsignalPlacement] {A : RustAlloc}
    (F0 : FsFiles) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (peer : AddrGhost) (σ : DpKitStk) :
    (cliPollSessKitPlaced A F0 Scope peer σ).Quiet :=
  ⟨fun _ _ _ => NoFsEv.nil, fun _ _ _ _ => NoFsEv.nil⟩

theorem cliPollIdPlaced_quiet [LibsignalPlacement] {A : RustAlloc}
    (F0 : FsFiles) (peer : AddrGhost) (σ : DpKitStk) :
    (cliPollIdKitPlaced A F0 peer σ).Quiet :=
  cliIdStoreSpecFullPlaced_quiet

theorem cliPollSelfPlaced_quiet [LibsignalPlacement] {A : RustAlloc}
    (F0 : FsFiles) (peer : AddrGhost) (σ : DpKitStk) :
    (cliPollSelfKitPlaced A F0 peer σ).Quiet :=
  cliIdSelfSpecFullPlaced_quiet

theorem cliPollPkPlaced_quiet [LibsignalPlacement] {A : RustAlloc}
    (F0 : FsFiles) (pid : BitVec 32) (σ : DpKitStk) :
    (cliPollPkKitPlaced A F0 pid σ).Quiet :=
  cliPreKeyStoreSpecPlaced_quiet cliIo.rd F0 cliWrOk pid
    σ.pkGetShim σ.pkGetPoll σ.pkRemoveShim σ.pkRemovePoll

theorem cliPollSpkPlaced_quiet [LibsignalPlacement] {A : RustAlloc}
    (F0 : FsFiles) (sid : BitVec 32) (σ : DpKitStk) :
    (cliPollSpkKitPlaced A F0 sid σ).Quiet :=
  cliSignedPreKeyStoreSpecPlaced_quiet cliIo.rd F0 cliWrOk sid σ.spkGetShim σ.spkGetPoll

theorem cliPollKpkPlaced_quiet [LibsignalPlacement] {A : RustAlloc}
    (F0 : FsFiles) (kid sid : BitVec 32) (kbk : PublicKey) (σ : DpKitStk) :
    (cliPollKpkKitPlaced A F0 kid sid kbk σ).Quiet :=
  cliKpkStoreSpecFullPlaced_quiet cliIo.rd F0 cliWrOk kid sid kbk
    σ.kpkGetShim σ.kpkGetPoll σ.kpkMarkShim σ.kpkMarkPoll

private theorem loadRec_of_cliPollSess_loadRel' {A : RustAlloc} {b : BitVec 64}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F0 : FsFiles} {peer : AddrGhost} {σ : DpKitStk}
    {opt : Option (SessionRecord (List (BitVec 8)))}
    (hinjK : Slots.EncodeInjOn Slots.scopeKit)
    (hsub : ∀ r, Scope r → Slots.scopeIn r)
    (hf : Slots.FilesOkPeer Scope F0 peer.val)
    (hrel : (cliPollSessKit A b F0 Slots.scopeKit peer σ).loadRel
      StoresGhost.opened.sessions peer.val (.ok opt)) :
    Slots.loadRec Scope F0 peer.val = .ok opt := by
  obtain ⟨bs, hget, hans⟩ := hrel
  have hans' : SessLoadAns Slots.scopeKit
      (StoresGhost.opened.sessions.get cliIo.rd F0 (Cli.addressText peer.val)) (.ok opt) := by
    rw [hget]; exact hans
  have h1 := (Slots.loadRec_unique hinjK hans').symm
  rwa [loadRec_scopeKit_eq hinjK hsub hf] at h1

theorem loadRec_of_cliPollSessPlaced_loadRel [LibsignalPlacement] {A : RustAlloc}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F0 : FsFiles} {peer : AddrGhost} {σ : DpKitStk}
    {opt : Option (SessionRecord (List (BitVec 8)))}
    (hinjK : Slots.EncodeInjOn Slots.scopeKit)
    (hsub : ∀ r, Scope r → Slots.scopeIn r)
    (hf : Slots.FilesOkPeer Scope F0 peer.val)
    (hrel : (cliPollSessKitPlaced A F0 Slots.scopeKit peer σ).loadRel
      StoresGhost.opened.sessions peer.val (.ok opt)) :
    Slots.loadRec Scope F0 peer.val = .ok opt :=
  loadRec_of_cliPollSess_loadRel' (A := A) (b := 0#64) (σ := σ) hinjK hsub hf hrel

theorem cliPollStageP1_fsAt_placed [LibsignalPlacement] {mmpl : Obj.MultiPlacement}
    {g : CliGhostHooks} {W : CliHooks}
    (hh : RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (F0 : FsFiles) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (peer : AddrGhost) (B : RunBudgets) {s : State} (hf : s.fs.files = F0) :
    FsAt
      (fun F => (cliPollSessKitPlaced E2E.HooksE.A0 F0 Scope peer (cliKitStk B)).envOk F ∧
                (cliPollIdKitPlaced E2E.HooksE.A0 F0 peer (cliKitStk B)).envOk F)
      ((cliPollSessKitPlaced E2E.HooksE.A0 F0 Scope peer (cliKitStk B)).Quiet ∧
       (cliPollIdKitPlaced E2E.HooksE.A0 F0 peer (cliKitStk B)).Quiet)
      (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) s :=
  .inr ⟨⟨cliPollSessPlaced_quiet F0 Scope peer (cliKitStk B),
         cliPollIdPlaced_quiet F0 peer (cliKitStk B)⟩,
        hh.fs (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) 518, ⟨hf, hf⟩⟩

theorem cliPollStageP4_fsAt_placed [LibsignalPlacement] {mmpl : Obj.MultiPlacement}
    {g : CliGhostHooks} {W : CliHooks}
    (hh : RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (F0 : FsFiles) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (peer : AddrGhost) (pid sid kid : BitVec 32) (kbk : PublicKey)
    (B : RunBudgets) {s : State} (hf : s.fs.files = F0) :
    FsAt
      (Cli.E2E.Pqxdh.ResponderClosure.Kits.stageP4EnvOk
        (cliPollSessKitPlaced E2E.HooksE.A0 F0 Scope peer (cliKitStk B))
        (cliPollIdKitPlaced E2E.HooksE.A0 F0 peer (cliKitStk B))
        (cliPollPkKitPlaced E2E.HooksE.A0 F0 pid (cliKitStk B))
        (cliPollKpkKitPlaced E2E.HooksE.A0 F0 kid sid kbk (cliKitStk B)))
      (Cli.E2E.Pqxdh.ResponderClosure.Kits.stageP4Quiet
        (cliPollSessKitPlaced E2E.HooksE.A0 F0 Scope peer (cliKitStk B))
        (cliPollIdKitPlaced E2E.HooksE.A0 F0 peer (cliKitStk B))
        (cliPollPkKitPlaced E2E.HooksE.A0 F0 pid (cliKitStk B))
        (cliPollKpkKitPlaced E2E.HooksE.A0 F0 kid sid kbk (cliKitStk B)))
      (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) s :=
  .inr ⟨⟨cliPollSessPlaced_quiet F0 Scope peer (cliKitStk B),
         cliPollIdPlaced_quiet F0 peer (cliKitStk B),
         cliPollPkPlaced_quiet F0 pid (cliKitStk B),
         cliPollKpkPlaced_quiet F0 kid sid kbk (cliKitStk B)⟩,
        hh.fs (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) 518, ⟨hf, hf, hf, hf⟩⟩

theorem cliPollStageP4Refused_fsAt_placed [LibsignalPlacement] {mmpl : Obj.MultiPlacement}
    {g : CliGhostHooks} {W : CliHooks}
    (hh : RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (F0 : FsFiles) (peer : AddrGhost) (kid sid : BitVec 32) (kbk : PublicKey)
    (B : RunBudgets) {s : State} (hf : s.fs.files = F0) :
    FsAt
      (fun F => (cliPollIdKitPlaced E2E.HooksE.A0 F0 peer (cliKitStk B)).envOk F ∧
                (cliPollKpkKitPlaced E2E.HooksE.A0 F0 kid sid kbk (cliKitStk B)).envOk F)
      ((cliPollIdKitPlaced E2E.HooksE.A0 F0 peer (cliKitStk B)).Quiet ∧
       (cliPollKpkKitPlaced E2E.HooksE.A0 F0 kid sid kbk (cliKitStk B)).Quiet)
      (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) s :=
  .inr ⟨⟨cliPollIdPlaced_quiet F0 peer (cliKitStk B),
         cliPollKpkPlaced_quiet F0 kid sid kbk (cliKitStk B)⟩,
        hh.fs (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) 518, ⟨hf, hf⟩⟩

/-! ## 3. Placed Vtable Bundles (`cliPoll*_vtablesPlacedOk` & `stageP1VtablesPlacedAt`) -/

theorem cliPollSess_vtablesPlacedOk [LibsignalPlacement] {A : RustAlloc}
    (F0 : FsFiles) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (peer : AddrGhost) (σ : DpKitStk) (hDropNz : lsmpl.base 547 ≠ 0#64) :
    SessionOnlyVtablesPlacedOk (cliPollSessKitPlaced A F0 Scope peer σ) :=
  cliSessionOnlyVtablesPlacedOk
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, lsDropOffPlaced_eq hDropNz, lsDropOffPlaced_eq hDropNz,
      rfl, rfl⟩

theorem cliPollId_vtablesPlacedOk [LibsignalPlacement] {A : RustAlloc}
    (F0 : FsFiles) (peer : AddrGhost) (σ : DpKitStk) (hDropNz : lsmpl.base 547 ≠ 0#64) :
    IdentityVtablesPlacedOk (cliPollIdKitPlaced A F0 peer σ) :=
  cliIdentityVtablesPlacedOk
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, lsDropOffPlaced_eq hDropNz, lsDropOffPlaced_eq hDropNz,
      rfl, rfl⟩

theorem cliPollPk_vtablesPlacedOk [LibsignalPlacement] {A : RustAlloc}
    (F0 : FsFiles) (pid : BitVec 32) (σ : DpKitStk) (hDropNz : lsmpl.base 547 ≠ 0#64) :
    PreKeyVtablesPlacedOk (cliPollPkKitPlaced A F0 pid σ) where
  getSlot hro hP := by
    simpa only [cliPollPkKitPlaced, cliPreKeyStoreSpecPlaced, BitVec.zero_add] using
      cliPkGetSlot_placed_ok hro hP
  removeSlot hro hP := by
    simpa only [cliPollPkKitPlaced, cliPreKeyStoreSpecPlaced, BitVec.zero_add] using
      cliPkRemoveSlot_placed_ok hro hP
  getFutDrop hro hP := by
    simpa only [cliPollPkKitPlaced, cliPreKeyStoreSpecPlaced, lsDropOffPlaced_eq hDropNz,
      BitVec.zero_add] using cliPkGetFutVt_placed_ok.drop hro hP
  getFutSize hro hP := by
    simpa only [cliPollPkKitPlaced, cliPreKeyStoreSpecPlaced, cliPreKeyStoreSpec, BitVec.zero_add] using
      cliPkGetFutVt_placed_ok.size hro hP
  getFutAlign hro hP := by
    simpa only [cliPollPkKitPlaced, cliPreKeyStoreSpecPlaced, BitVec.zero_add] using
      cliPkGetFutVt_placed_ok.align hro hP
  getFutPoll hro hP := by
    simpa only [cliPollPkKitPlaced, cliPreKeyStoreSpecPlaced, BitVec.zero_add] using
      cliPkGetFutVt_placed_ok.poll hro hP
  removeFutDrop hro hP := by
    simpa only [cliPollPkKitPlaced, cliPreKeyStoreSpecPlaced, lsDropOffPlaced_eq hDropNz,
      BitVec.zero_add] using cliPkRemoveFutVt_placed_ok.drop hro hP
  removeFutSize hro hP := by
    simpa only [cliPollPkKitPlaced, cliPreKeyStoreSpecPlaced, cliPreKeyStoreSpec, BitVec.zero_add] using
      cliPkRemoveFutVt_placed_ok.size hro hP
  removeFutAlign hro hP := by
    simpa only [cliPollPkKitPlaced, cliPreKeyStoreSpecPlaced, BitVec.zero_add] using
      cliPkRemoveFutVt_placed_ok.align hro hP
  removeFutPoll hro hP := by
    simpa only [cliPollPkKitPlaced, cliPreKeyStoreSpecPlaced, BitVec.zero_add] using
      cliPkRemoveFutVt_placed_ok.poll hro hP

theorem cliPollSpk_vtablesPlacedOk [LibsignalPlacement] {A : RustAlloc}
    (F0 : FsFiles) (sid : BitVec 32) (σ : DpKitStk) (hDropNz : lsmpl.base 547 ≠ 0#64) :
    SignedPreKeyVtablesPlacedOk (cliPollSpkKitPlaced A F0 sid σ) where
  getSlot hro hP := by
    simpa only [cliPollSpkKitPlaced, cliSignedPreKeyStoreSpecPlaced, BitVec.zero_add] using
      cliSpkGetSlot_placed_ok hro hP
  getFutDrop hro hP := by
    simpa only [cliPollSpkKitPlaced, cliSignedPreKeyStoreSpecPlaced, lsDropOffPlaced_eq hDropNz,
      BitVec.zero_add] using cliSpkGetFutVt_placed_ok.drop hro hP
  getFutSize hro hP := by
    simpa only [cliPollSpkKitPlaced, cliSignedPreKeyStoreSpecPlaced, cliSignedPreKeyStoreSpec,
      BitVec.zero_add] using cliSpkGetFutVt_placed_ok.size hro hP
  getFutAlign hro hP := by
    simpa only [cliPollSpkKitPlaced, cliSignedPreKeyStoreSpecPlaced, BitVec.zero_add] using
      cliSpkGetFutVt_placed_ok.align hro hP
  getFutPoll hro hP := by
    simpa only [cliPollSpkKitPlaced, cliSignedPreKeyStoreSpecPlaced, BitVec.zero_add] using
      cliSpkGetFutVt_placed_ok.poll hro hP

theorem cliPollKpk_vtablesPlacedOk [LibsignalPlacement] {A : RustAlloc}
    (F0 : FsFiles) (kid sid : BitVec 32) (kbk : PublicKey) (σ : DpKitStk)
    (hDropNz : lsmpl.base 547 ≠ 0#64) :
    KyberPreKeyVtablesPlacedOk (cliPollKpkKitPlaced A F0 kid sid kbk σ) where
  getSlot hro hP := by
    simpa only [cliPollKpkKitPlaced, cliKpkStoreSpecFullPlaced, cliKyberPreKeyStoreSpecPlaced,
      BitVec.zero_add] using cliKpkGetSlot_placed_ok hro hP
  markSlot hro hP := by
    simpa only [cliPollKpkKitPlaced, cliKpkStoreSpecFullPlaced, cliKyberPreKeyStoreSpecPlaced,
      BitVec.zero_add] using cliKpkMarkSlot_placed_ok hro hP
  getFutDrop hro hP := by
    simpa only [cliPollKpkKitPlaced, cliKpkStoreSpecFullPlaced, cliKyberPreKeyStoreSpecPlaced,
      lsDropOffPlaced_eq hDropNz, BitVec.zero_add] using cliKpkGetFutVt_placed_ok.drop hro hP
  getFutSize hro hP := by
    simpa only [cliPollKpkKitPlaced, cliKpkStoreSpecFullPlaced, cliKyberPreKeyStoreSpecPlaced,
      cliKyberPreKeyStoreSpec, cliKpkStoreSpec, BitVec.zero_add] using
      cliKpkGetFutVt_placed_ok.size hro hP
  getFutAlign hro hP := by
    simpa only [cliPollKpkKitPlaced, cliKpkStoreSpecFullPlaced, cliKyberPreKeyStoreSpecPlaced,
      BitVec.zero_add] using cliKpkGetFutVt_placed_ok.align hro hP
  getFutPoll hro hP := by
    simpa only [cliPollKpkKitPlaced, cliKpkStoreSpecFullPlaced, cliKyberPreKeyStoreSpecPlaced,
      BitVec.zero_add] using cliKpkGetFutVt_placed_ok.poll hro hP
  markFutDrop hro hP := by
    simpa only [cliPollKpkKitPlaced, cliKpkStoreSpecFullPlaced, cliKyberPreKeyStoreSpecPlaced,
      lsDropOffPlaced_eq hDropNz, BitVec.zero_add] using cliKpkMarkFutVt_placed_ok.drop hro hP
  markFutSize hro hP := by
    simpa only [cliPollKpkKitPlaced, cliKpkStoreSpecFullPlaced, cliKyberPreKeyStoreSpecPlaced,
      cliKyberPreKeyStoreSpec, cliKpkStoreSpec, BitVec.zero_add] using
      cliKpkMarkFutVt_placed_ok.size hro hP
  markFutAlign hro hP := by
    simpa only [cliPollKpkKitPlaced, cliKpkStoreSpecFullPlaced, cliKyberPreKeyStoreSpecPlaced,
      BitVec.zero_add] using cliKpkMarkFutVt_placed_ok.align hro hP
  markFutPoll hro hP := by
    simpa only [cliPollKpkKitPlaced, cliKpkStoreSpecFullPlaced, cliKyberPreKeyStoreSpecPlaced,
      BitVec.zero_add] using cliKpkMarkFutVt_placed_ok.poll hro hP

theorem cliPollSelf_vtablesPlacedOk [LibsignalPlacement] {A : RustAlloc}
    (F0 : FsFiles) (peer : AddrGhost) (σ : DpKitStk) (hDropNz : lsmpl.base 547 ≠ 0#64) :
    IdentitySelfVtablesPlacedOk
      (cliPollIdKitPlaced A F0 peer σ) (cliPollSelfKitPlaced A F0 peer σ) where
  kpSlot hro hP := by
    simpa only [cliPollIdKitPlaced, cliIdStoreSpecFullPlaced, cliPollSelfKitPlaced,
      cliIdSelfSpecFullPlaced, BitVec.zero_add] using cliIdKpSlot_placed_ok hro hP
  regIdSlot hro hP := by
    simpa only [cliPollIdKitPlaced, cliIdStoreSpecFullPlaced, cliPollSelfKitPlaced,
      cliIdSelfSpecFullPlaced, BitVec.zero_add] using cliIdRegIdSlot_placed_ok hro hP
  kpFutDrop hro hP := by
    simpa only [cliPollSelfKitPlaced, cliIdSelfSpecFullPlaced, lsDropOffPlaced_eq hDropNz,
      BitVec.zero_add] using cliIdKpFutDrop_placed_ok hro hP
  kpFutSize hro hP := by
    simpa only [cliPollSelfKitPlaced, cliIdSelfSpecFullPlaced, BitVec.zero_add] using
      cliIdKpFutSize_placed_ok hro hP
  kpFutAlign hro hP := by
    simpa only [cliPollSelfKitPlaced, cliIdSelfSpecFullPlaced, BitVec.zero_add] using
      cliIdKpFutAlign_placed_ok hro hP
  kpFutPoll hro hP := by
    simpa only [cliPollSelfKitPlaced, cliIdSelfSpecFullPlaced, BitVec.zero_add] using
      cliIdKpFutPoll_placed_ok hro hP
  regIdFutDrop hro hP := by
    simpa only [cliPollSelfKitPlaced, cliIdSelfSpecFullPlaced, lsDropOffPlaced_eq hDropNz,
      BitVec.zero_add] using cliIdRegIdFutDrop_placed_ok hro hP
  regIdFutSize hro hP := by
    simpa only [cliPollSelfKitPlaced, cliIdSelfSpecFullPlaced, BitVec.zero_add] using
      cliIdRegIdFutSize_placed_ok hro hP
  regIdFutAlign hro hP := by
    simpa only [cliPollSelfKitPlaced, cliIdSelfSpecFullPlaced, BitVec.zero_add] using
      cliIdRegIdFutAlign_placed_ok hro hP
  regIdFutPoll hro hP := by
    simpa only [cliPollSelfKitPlaced, cliIdSelfSpecFullPlaced, BitVec.zero_add] using
      cliIdRegIdFutPoll_placed_ok hro hP

/-- Read-only vtable cells required by Stage P1 at `b := 0#64`. -/
def stageP1VtablesPlacedAt {A : RustAlloc}
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64) : SepProp :=
  ((kit.ss_vt + 0x18#64) ↦₆₄ᵣ (0#64 + kit.loadShimOff)) ∗
  ((ikit.id_vt + 0x30#64) ↦₆₄ᵣ (0#64 + ikit.trustShimOff)) ∗
  ((0#64 + kit.loadFutVtOff) ↦₆₄ᵣ (0#64 + kit.loadFutDropOff)) ∗
  ((0#64 + kit.loadFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.loadBoxSize) ∗
  ((0#64 + kit.loadFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
  ((0#64 + kit.loadFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + kit.loadPollOff)) ∗
  ((0#64 + ikit.trustFutVtOff) ↦₆₄ᵣ (0#64 + ikit.trustFutDropOff)) ∗
  ((0#64 + ikit.trustFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.trustBoxSize) ∗
  ((0#64 + ikit.trustFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
  ((0#64 + ikit.trustFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + ikit.trustPollOff))

theorem satisfies_stageP1VtablesPlacedAt [LibsignalPlacement] {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    (hsess : SessionOnlyVtablesPlacedOk kit)
    (hid : IdentityVtablesPlacedOk ikit)
    {m : Memory} {P : SepProp}
    (hro : CryptoVerification.LibsignalRoLoaded lsmpl m) (hP : m ⊨ P) :
    m ⊨ stageP1VtablesPlacedAt kit ikit ∗ P := by
  have h10 := hid.trustFutPoll hro hP
  have h9 := hid.trustFutAlign hro h10
  have h8 := hid.trustFutSize hro h9
  have h7 := hid.trustFutDrop hro h8
  have h6 := hsess.loadFutPoll hro h7
  have h5 := hsess.loadFutAlign hro h6
  have h4 := hsess.loadFutSize hro h5
  have h3 := hsess.loadFutDrop hro h4
  have h2 := hid.trustSlot hro h3
  have h1 := hsess.loadSlot hro h2
  dsimp only [stageP1VtablesPlacedAt]
  simpa only [sepConj_assoc] using h1

end CryptoVerification.SignalSession.Cli.RunProofs.Poll
