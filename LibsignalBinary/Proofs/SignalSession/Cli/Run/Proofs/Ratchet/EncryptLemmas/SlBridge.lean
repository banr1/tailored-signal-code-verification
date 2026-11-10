/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.StoreDet
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOk
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOk
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seams
public import LibsignalBinary.Proofs.SignalSession.Cli.Fs
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.SpeOwnedBridges

/-!
# Separation-Logic, Stack-Budget, and Trace Bridges for `encrypt`

Connects the outer `encSlotSpec` framing (`storesAt`, `coinsInstalled`, `encResAt`, `slotTrace`) to
the inner `withStoresEncSpecV` contract and CLI store kits `w1SessKit` and `w1IdKit`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false

namespace CryptoVerification.SignalSession.Cli.RunProofs.EncryptLemmas

open Arm64 Arm64.Process ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.KitInst
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity

/-! ## CLI store kits and stack budget bound -/

abbrev w1SessKit (B : RunBudgets) (img : Obj.Image) (F : FsFiles) (peer : AddrGhost) :
    SessionStoreSpec E2E.HooksE.A0 img.base :=
  cliSessionStoreSpec E2E.HooksE.A0 img.base cliIo.rd F cliWrOk Slots.scopeKit peer
    SessKit.loadShimNeed (SessKit.loadPollNeed B.readFile)
    SessKit.storeShimNeed SessKit.storePollNeedX

abbrev w1IdKit (B : RunBudgets) (img : Obj.Image) (F : FsFiles) (peer : AddrGhost) :
    IdentityStoreSpec E2E.HooksE.A0 img.base :=
  cliIdentityStoreSpec E2E.HooksE.A0 img.base cliIo.rd F cliWrOk peer
    IdKit.trustShimNeed (IdKit.trustPollNeed B.readFile)
    IdKit.saveShimNeed (IdKit.savePollNeed B.readFile)

/-- The inner `withStoresEncStackV` stack requirement of `w1SessKit` and `w1IdKit` fits within `w1EncryptNeed B = 2^20 + B.readFile`. -/
theorem w1_innerStack_le_need (B : RunBudgets) (img : Obj.Image) (F : FsFiles) (peer : AddrGhost) :
    withStoresEncStackV (w1SessKit B img F peer) (w1IdKit B img F peer) ≤ w1EncryptNeed B := by
  have hdg : RunBudgets.dirGetNeed ⟨B.readFile⟩ ≤ 2 ^ 19 + B.readFile := by
    simp only [RunBudgets.dirGetNeed]
    have h1 : pathNeed ≤ 2 ^ 18 := by decide
    have h2 : extHookStack ≤ 2 ^ 18 := by decide
    omega
  have hlp : SessKit.loadPollNeed B.readFile ≤ 2 ^ 19 + 0x350 + B.readFile := by
    simp only [SessKit.loadPollNeed]
    have h1 : SessKit.addrTextNeed ≤ 2 ^ 19 := by decide
    have h2 : E2E.Record.recDeserializeStack ≤ 2 ^ 19 := by decide
    have h3 : extHookStack ≤ 2 ^ 19 := by decide
    omega
  have htp : IdKit.trustPollNeed B.readFile ≤ 2 ^ 19 + 0xc0 + B.readFile := by
    simp only [IdKit.trustPollNeed]
    have h1 : extHookStack ≤ 2 ^ 19 := by decide
    omega
  have hsp : IdKit.savePollNeed B.readFile ≤ 2 ^ 19 + 0xd0 + B.readFile := by
    simp only [IdKit.savePollNeed]
    have h1 : IdKit.dirPutStrNeed ≤ 2 ^ 19 := by decide
    have h2 : publicKeySerializeStackX ≤ 2 ^ 19 := by decide
    have h3 : extHookStack ≤ 2 ^ 19 := by decide
    omega
  have henc : encSubStack = 521200 := by decide
  have hfrm : encFrameSize = 3040 := by decide
  have xls : SessKit.loadShimNeed ≤ 2 ^ 19 := by decide
  have xss : SessKit.storeShimNeed ≤ 2 ^ 19 := by decide
  have xst : SessKit.storePollNeedX ≤ 2 ^ 19 := by decide
  have xts : IdKit.trustShimNeed ≤ 2 ^ 19 := by decide
  have xsv : IdKit.saveShimNeed ≤ 2 ^ 19 := by decide
  dsimp only [withStoresEncStackV, encSubStackV, w1SessKit, w1IdKit,
    cliSessionStoreSpec, cliIdentityStoreSpec, w1EncryptNeed]
  omega

/-! ## Entry and exit `storesAt` framing -/

/-- The five `Dir`s of `Stores` untouched by `encrypt`: `signed` (`+0x50`), `kyber.oneTime` (`+0x78`),
`kyber.lastResort` (`+0xa0`), `oneTime` (`+0xc8`), and `pub` (`+0x118`). -/
def w1UnusedDirsAt (A : RustAlloc) (a : BitVec 64) (g : StoresGhost) : SepProp :=
  dirAt A (a + 0x50#64) g.signed ∗
    dirAt A (a + 0x78#64) g.kyber.oneTime ∗
    dirAt A (a + 0xa0#64) g.kyber.lastResort ∗
    dirAt A (a + 0xc8#64) g.oneTime ∗
    dirAt A (a + 0x118#64) g.pub

theorem cliSessInv_opened_wrOk {Scope : SessionRecord (List (BitVec 8)) → Prop} {F : FsFiles}
    {peer : AddrGhost} (hsub : ∀ r, Scope r → Slots.scopeIn r)
    (hok : Slots.FilesOkPeer Scope F peer.val) :
    CliSessInv cliIo.rd F cliWrOk Slots.scopeKit peer StoresGhost.opened.sessions := by
  have hbase := Slots.cliSessInv_opened (peer := peer) (filesOkPeer_mono (scopeKit_of_sub hsub) hok)
  exact ⟨hbase.nameLt, hbase.textLt, hbase.pathLt, ⟨hok.sessPathOk, hok.sessPathLt⟩,
    hbase.getOk, hbase.changedLt⟩

theorem cliIdInv_opened_wrOk {Scope : SessionRecord (List (BitVec 8)) → Prop} {F : FsFiles}
    {peer : AddrGhost} (hok : Slots.FilesOkPeer Scope F peer.val) :
    CliIdInv cliIo.rd F cliWrOk peer StoresGhost.opened.identity := by
  have hbase := Slots.cliIdInv_opened (peer := peer) hok
  exact ⟨hbase.nameLt, hbase.pathLt, ⟨hok.idPathOk, hok.idPathLt⟩, hbase.getOk, hbase.changedLt⟩

theorem storesAt_opened_to_kits {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (B : RunBudgets) (img : Obj.Image) (F : FsFiles) (peer : AddrGhost) (a : BitVec 64)
    (hsub : ∀ r, Scope r → Slots.scopeIn r)
    (hok : Slots.FilesOkPeer Scope F peer.val) :
    storesAt E2E.HooksE.A0 a StoresGhost.opened ⊢
      (w1SessKit B img F peer).storeAt (a + 0xf0#64) StoresGhost.opened.sessions ∗
        (w1IdKit B img F peer).identityAt a StoresGhost.opened.identity ∗
        w1UnusedDirsAt E2E.HooksE.A0 a StoresGhost.opened := by
  have hsInv := cliSessInv_opened_wrOk (peer := peer) hsub hok
  have hiInv := cliIdInv_opened_wrOk (peer := peer) hok
  dsimp only [w1SessKit, w1IdKit, cliSessionStoreSpec, cliIdentityStoreSpec,
    cliSessStoreAt, cliIdStoreAt, w1UnusedDirsAt, storesAt]
  rw [pure_sepConj_of_true hsInv, pure_sepConj_of_true hiInv]
  exact Entails.of_eq (by ac_rfl)

theorem kits_to_storesAt (B : RunBudgets) (img : Obj.Image) (F : FsFiles) (peer : AddrGhost)
    (a : BitVec 64) (sess : DirGhost) (idg : IdGhost) :
    (w1SessKit B img F peer).storeAt (a + 0xf0#64) sess ∗
      (w1IdKit B img F peer).identityAt a idg ∗
      w1UnusedDirsAt E2E.HooksE.A0 a StoresGhost.opened ⊢
      storesAt E2E.HooksE.A0 a (mkCliStores sess idg) := by
  dsimp only [w1SessKit, w1IdKit, cliSessionStoreSpec, cliIdentityStoreSpec,
    cliSessStoreAt, cliIdStoreAt, w1UnusedDirsAt, storesAt, mkCliStores]
  have hperm :
      (⌜CliSessInv cliIo.rd F cliWrOk Slots.scopeKit peer sess⌝ ∗ dirAt E2E.HooksE.A0 (a + 0xf0#64) sess) ∗
        (⌜CliIdInv cliIo.rd F cliWrOk peer idg⌝ ∗ dirAt E2E.HooksE.A0 a idg.own ∗
          dirAt E2E.HooksE.A0 (a + 0x28#64) idg.peers) ∗
        (dirAt E2E.HooksE.A0 (a + 0x50#64) StoresGhost.opened.signed ∗
          dirAt E2E.HooksE.A0 (a + 0x78#64) StoresGhost.opened.kyber.oneTime ∗
          dirAt E2E.HooksE.A0 (a + 0xa0#64) StoresGhost.opened.kyber.lastResort ∗
          dirAt E2E.HooksE.A0 (a + 0xc8#64) StoresGhost.opened.oneTime ∗
          dirAt E2E.HooksE.A0 (a + 0x118#64) StoresGhost.opened.pub) =
      ⌜CliSessInv cliIo.rd F cliWrOk Slots.scopeKit peer sess⌝ ∗
        (⌜CliIdInv cliIo.rd F cliWrOk peer idg⌝ ∗
          (dirAt E2E.HooksE.A0 a idg.own ∗
            dirAt E2E.HooksE.A0 (a + 0x28#64) idg.peers ∗
            dirAt E2E.HooksE.A0 (a + 0x50#64) StoresGhost.opened.signed ∗
            dirAt E2E.HooksE.A0 (a + 0x78#64) StoresGhost.opened.kyber.oneTime ∗
            dirAt E2E.HooksE.A0 (a + 0xa0#64) StoresGhost.opened.kyber.lastResort ∗
            dirAt E2E.HooksE.A0 (a + 0xc8#64) StoresGhost.opened.oneTime ∗
            dirAt E2E.HooksE.A0 (a + 0xf0#64) sess ∗
            dirAt E2E.HooksE.A0 (a + 0x118#64) StoresGhost.opened.pub)) := by ac_rfl
  rw [hperm]
  exact Entails.pure_left fun _ => Entails.pure_left fun _ => Entails.refl _

/-! ## Result conversion and `< 2^40` wire bound extraction -/

theorem apiEncResultAt_to_encResAt (A : RustAlloc) (r : BitVec 64)
    (e : Except (ApiError AddrVal Unit) CiphertextMessage) (he : e ≠ .error (.store ())) :
    apiEncResultAt A r e ⊢ encResAt A r e := by
  cases e with
  | ok m => exact Entails.of_eq (encResAt_ok A r m).symm
  | error err =>
    exact apiEncResultAt_err_owned A r err (fun h => he (congrArg Except.error h))

/-- Spatially extracts `m.message.serialized.length < 2^40` from `apiEncResultAt A r (.ok (.preKeySignalMessage m)) ∗ R`. -/
theorem preKeyMsg_inner_serialized_lt_of_mem {A : RustAlloc} {r : BitVec 64}
    {m : PreKeySignalMessage} {R : SepProp} {mem : Memory}
    (hm : mem ⊨ apiEncResultAt A r (.ok (.preKeySignalMessage m)) ∗ R) :
    m.message.serialized.length < 2 ^ 40 := by
  dsimp only [apiEncResultAt, preKeyMsgAt, signalMessageAt] at hm
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm
  obtain ⟨g, hg⟩ := hm
  simp only [sepConj_assoc] at hg
  rw [satisfies_pure_sepConj] at hg
  exact hg.1.2.1

/-! ## `slotTrace` from `FsInv` and trace preservation -/

theorem slotTrace_of_fsInv_trace_eq {s0 sf : State}
    (hinv : FsInv s0.fs.files s0.trace sf) (htr : sf.trace = s0.trace) :
    slotTrace s0 sf := by
  refine ⟨htr ▸ List.prefix_refl _, ?_, by rw [htr]⟩
  have htr_append : sf.trace = s0.trace ++ [] := by simp [htr]
  exact files_eq_at_callback hinv htr_append NoFsEv.nil

/-! ## Allocator-parametric generalization -/

abbrev w1SessKitExt (A : RustAlloc) (B : RunBudgets) (img : Obj.Image) (F : FsFiles)
    (peer : AddrGhost) : SessionStoreSpec A img.base :=
  cliSessionStoreSpec A img.base cliIo.rd F cliWrOk Slots.scopeKit peer
    SessKit.loadShimNeed (SessKit.loadPollNeed B.readFile)
    SessKit.storeShimNeed SessKit.storePollNeedX

abbrev w1IdKitExt (A : RustAlloc) (B : RunBudgets) (img : Obj.Image) (F : FsFiles)
    (peer : AddrGhost) : IdentityStoreSpec A img.base :=
  cliIdentityStoreSpec A img.base cliIo.rd F cliWrOk peer
    IdKit.trustShimNeed (IdKit.trustPollNeed B.readFile)
    IdKit.saveShimNeed (IdKit.savePollNeed B.readFile)

theorem w1SessKitExt_A0 (B : RunBudgets) (img : Obj.Image) (F : FsFiles) (peer : AddrGhost) :
    w1SessKitExt E2E.HooksE.A0 B img F peer = w1SessKit B img F peer :=
  rfl

theorem w1IdKitExt_A0 (B : RunBudgets) (img : Obj.Image) (F : FsFiles) (peer : AddrGhost) :
    w1IdKitExt E2E.HooksE.A0 B img F peer = w1IdKit B img F peer :=
  rfl

theorem w1_innerStack_le_need_ext (A : RustAlloc) (B : RunBudgets) (img : Obj.Image)
    (F : FsFiles) (peer : AddrGhost) :
    withStoresEncStackV (w1SessKitExt A B img F peer) (w1IdKitExt A B img F peer) ≤
      w1EncryptNeed B := by
  have h := w1_innerStack_le_need B img F peer
  simpa only [withStoresEncStackV, encSubStackV, w1SessKitExt, w1IdKitExt, w1SessKit, w1IdKit,
    cliSessionStoreSpec, cliIdentityStoreSpec] using h

theorem storesAt_opened_to_kits_ext {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (A : RustAlloc) (B : RunBudgets) (img : Obj.Image) (F : FsFiles) (peer : AddrGhost)
    (a : BitVec 64)
    (hsub : ∀ r, Scope r → Slots.scopeIn r)
    (hok : Slots.FilesOkPeer Scope F peer.val) :
    storesAt A a StoresGhost.opened ⊢
      (w1SessKitExt A B img F peer).storeAt (a + 0xf0#64) StoresGhost.opened.sessions ∗
        (w1IdKitExt A B img F peer).identityAt a StoresGhost.opened.identity ∗
        w1UnusedDirsAt A a StoresGhost.opened := by
  have hsInv := cliSessInv_opened_wrOk (peer := peer) hsub hok
  have hiInv := cliIdInv_opened_wrOk (peer := peer) hok
  dsimp only [w1SessKitExt, w1IdKitExt, cliSessionStoreSpec, cliIdentityStoreSpec,
    cliSessStoreAt, cliIdStoreAt, w1UnusedDirsAt, storesAt]
  rw [pure_sepConj_of_true hsInv, pure_sepConj_of_true hiInv]
  exact Entails.of_eq (by ac_rfl)

theorem kits_to_storesAt_ext (A : RustAlloc) (B : RunBudgets) (img : Obj.Image) (F : FsFiles)
    (peer : AddrGhost) (a : BitVec 64) (sess : DirGhost) (idg : IdGhost) :
    (w1SessKitExt A B img F peer).storeAt (a + 0xf0#64) sess ∗
      (w1IdKitExt A B img F peer).identityAt a idg ∗
      w1UnusedDirsAt A a StoresGhost.opened ⊢
      storesAt A a (mkCliStores sess idg) := by
  dsimp only [w1SessKitExt, w1IdKitExt, cliSessionStoreSpec, cliIdentityStoreSpec,
    cliSessStoreAt, cliIdStoreAt, w1UnusedDirsAt, storesAt, mkCliStores]
  have hperm :
      (⌜CliSessInv cliIo.rd F cliWrOk Slots.scopeKit peer sess⌝ ∗ dirAt A (a + 0xf0#64) sess) ∗
        (⌜CliIdInv cliIo.rd F cliWrOk peer idg⌝ ∗ dirAt A a idg.own ∗
          dirAt A (a + 0x28#64) idg.peers) ∗
        (dirAt A (a + 0x50#64) StoresGhost.opened.signed ∗
          dirAt A (a + 0x78#64) StoresGhost.opened.kyber.oneTime ∗
          dirAt A (a + 0xa0#64) StoresGhost.opened.kyber.lastResort ∗
          dirAt A (a + 0xc8#64) StoresGhost.opened.oneTime ∗
          dirAt A (a + 0x118#64) StoresGhost.opened.pub) =
      ⌜CliSessInv cliIo.rd F cliWrOk Slots.scopeKit peer sess⌝ ∗
        (⌜CliIdInv cliIo.rd F cliWrOk peer idg⌝ ∗
          (dirAt A a idg.own ∗
            dirAt A (a + 0x28#64) idg.peers ∗
            dirAt A (a + 0x50#64) StoresGhost.opened.signed ∗
            dirAt A (a + 0x78#64) StoresGhost.opened.kyber.oneTime ∗
            dirAt A (a + 0xa0#64) StoresGhost.opened.kyber.lastResort ∗
            dirAt A (a + 0xc8#64) StoresGhost.opened.oneTime ∗
            dirAt A (a + 0xf0#64) sess ∗
            dirAt A (a + 0x118#64) StoresGhost.opened.pub)) := by ac_rfl
  rw [hperm]
  exact Entails.pure_left fun _ => Entails.pure_left fun _ => Entails.refl _

/-- Every session in `Slots.scopeKit` has `p.timestamp = 0` on any pending pre-key
(`SessionScopeP`), discharging `EncEnvT_ext.scopeTsZero`. -/
theorem w1_scopeKit_pendingPreKey_ts_zero {A : RustAlloc} {B : RunBudgets} {img : Obj.Image}
    {F : FsFiles} {peer : AddrGhost} {st0 : (w1SessKitExt A B img F peer).StoreState}
    {rem : AddrVal} (r : SessionRecord (List (BitVec 8))) (s : Session (List (BitVec 8)))
    (p : PendingPreKey)
    (hsc : (w1SessKitExt A B img F peer).ScopeAt Slots.scopeKit st0 rem r)
    (hs : r.currentSession = some s)
    (hp : s.pendingPreKey = some p) :
    p.timestamp = 0 := by
  obtain ⟨s', hs', hsp⟩ := hsc.1.2
  cases hs.symm.trans hs'
  exact hsp.2.1 p hp

end CryptoVerification.SignalSession.Cli.RunProofs.EncryptLemmas
