/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StoresAt
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4KyberRefused
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitE
public import LibsignalBinary.Proofs.PublicApi.StoreKit.SignedPreKeyStoreKitE
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.LoadRec
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ScopeIn
import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityFutDropExt
import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCli
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.InitInv
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.KitCodecs

/-!
# CLI Store Vtable and `KitOk` Bundles for Poll Closure

Proves vtable offset equalities, store quietness, spatial `stageP1VtablesAt` introduction, and
`KitOk` / `FsAt` discharges for all six CLI poll store kits (`cliPoll*Kit` and `Ext` variants).
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

/-- `cliPollSessKit` has the exact CLI session vtable/shim/poll/drop offsets. -/
theorem cliPollSessKit_offsets {A : RustAlloc} (img : Obj.Image) (F0 : FsFiles)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (peer : AddrGhost) (σ : DpKitStk) :
    CliSessKitOffsets img (cliPollSessKit A img.base F0 Scope peer σ) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `cliPollIdKit` has the exact CLI identity vtable/shim/poll/drop offsets. -/
theorem cliPollIdKit_offsets {A : RustAlloc} (img : Obj.Image) (F0 : FsFiles)
    (peer : AddrGhost) (σ : DpKitStk) :
    CliIdKitOffsets img (cliPollIdKit A img.base F0 peer σ) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem cliPollSess_vtablesOk {A : RustAlloc} {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img)
    (F0 : FsFiles) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (peer : AddrGhost) (σ : DpKitStk) :
    MessageDecrypt.SessionOnlyVtablesOk img (cliPollSessKit A img.base F0 Scope peer σ) :=
  cliSessionOnlyVtablesOk himg (cliPollSessKit_offsets img F0 Scope peer σ)

theorem cliPollId_vtablesOk {A : RustAlloc} {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img)
    (F0 : FsFiles) (peer : AddrGhost) (σ : DpKitStk) :
    IdentityVtablesOk img (cliPollIdKit A img.base F0 peer σ) :=
  cliIdentityVtablesOk himg (cliPollIdKit_offsets img F0 peer σ)

theorem cliPollPk_vtablesOk {A : RustAlloc} {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img)
    (F0 : FsFiles) (pid : BitVec 32) (σ : DpKitStk) :
    PreKeyVtablesOk img (cliPollPkKit A img.base F0 pid σ) :=
  cliPreKeyStoreSpec_vtablesOk himg cliIo.rd F0 cliWrOk pid
    σ.pkGetShim σ.pkGetPoll σ.pkRemoveShim σ.pkRemovePoll

theorem cliPollSpk_vtablesOk {A : RustAlloc} {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img)
    (F0 : FsFiles) (sid : BitVec 32) (σ : DpKitStk) :
    SignedPreKeyVtablesOk img (cliPollSpkKit A img.base F0 sid σ) :=
  cliSignedPreKeyStoreSpec_vtablesOk himg cliIo.rd F0 cliWrOk sid
    σ.spkGetShim σ.spkGetPoll

theorem cliPollSelf_vtablesOk {A : RustAlloc} {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img)
    (F0 : FsFiles) (peer : AddrGhost) (σ : DpKitStk) :
    StoreKit.IdentitySelf.IdentitySelfVtablesOk img
      (cliPollIdKit A img.base F0 peer σ)
      (cliPollSelfKit A img.base F0 peer σ) :=
  cliIdSelfSpecFull_vtablesOk himg

theorem cliPollKpk_vtablesOk {A : RustAlloc} {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img)
    (F0 : FsFiles) (kid sid : BitVec 32) (kbk : PublicKey) (σ : DpKitStk) :
    KyberPreKeyVtablesOk img (cliPollKpkKit A img.base F0 kid sid kbk σ) :=
  cliKpkStoreSpecFull_vtablesOk himg cliIo.rd F0 cliWrOk kid sid kbk
    σ.kpkGetShim σ.kpkGetPoll σ.kpkMarkShim σ.kpkMarkPoll

/-! ## Quietness for All 6 CLI Poll Kits -/

theorem cliPollSess_quiet {A : RustAlloc} (b : BitVec 64)
    (F0 : FsFiles) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (peer : AddrGhost) (σ : DpKitStk) :
    (cliPollSessKit A b F0 Scope peer σ).Quiet :=
  ⟨fun _ _ _ => NoFsEv.nil, fun _ _ _ _ => NoFsEv.nil⟩

theorem cliPollId_quiet {A : RustAlloc} {img : Obj.Image}
    (F0 : FsFiles) (peer : AddrGhost) (σ : DpKitStk) :
    (cliPollIdKit A img.base F0 peer σ).Quiet :=
  cliIdStoreSpecFull_quiet

theorem cliPollSelf_quiet {A : RustAlloc} {img : Obj.Image}
    (F0 : FsFiles) (peer : AddrGhost) (σ : DpKitStk) :
    (cliPollSelfKit A img.base F0 peer σ).Quiet :=
  cliIdSelfSpecFull_quiet

theorem cliPollPk_quiet {A : RustAlloc} (b : BitVec 64)
    (F0 : FsFiles) (pid : BitVec 32) (σ : DpKitStk) :
    (cliPollPkKit A b F0 pid σ).Quiet :=
  cliPreKeyStoreSpec_quiet cliIo.rd F0 cliWrOk pid
    σ.pkGetShim σ.pkGetPoll σ.pkRemoveShim σ.pkRemovePoll

theorem cliPollSpk_quiet {A : RustAlloc} (b : BitVec 64)
    (F0 : FsFiles) (sid : BitVec 32) (σ : DpKitStk) :
    (cliPollSpkKit A b F0 sid σ).Quiet :=
  cliSignedPreKeyStoreSpec_quiet cliIo.rd F0 cliWrOk sid σ.spkGetShim σ.spkGetPoll

theorem cliPollKpk_quiet {A : RustAlloc} (b : BitVec 64)
    (F0 : FsFiles) (kid sid : BitVec 32) (kbk : PublicKey) (σ : DpKitStk) :
    (cliPollKpkKit A b F0 kid sid kbk σ).Quiet :=
  cliKpkStoreSpecFull_quiet cliIo.rd F0 cliWrOk kid sid kbk
    σ.kpkGetShim σ.kpkGetPoll σ.kpkMarkShim σ.kpkMarkPoll

/-! ## Spatial Stage P1 Vtable Bundle -/

/-- Read-only vtable cells required by Stage P1 (`stageP1_ok_kit` and `stageP1_untrusted_ok_kit`). -/
def stageP1VtablesAt {A : RustAlloc} (img : Obj.Image)
    (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base) : SepProp :=
  ((kit.ss_vt + 0x18#64) ↦₆₄ᵣ (img.base + kit.loadShimOff)) ∗
  ((ikit.id_vt + 0x30#64) ↦₆₄ᵣ (img.base + ikit.trustShimOff)) ∗
  ((img.base + kit.loadFutVtOff) ↦₆₄ᵣ (img.base + kit.loadFutDropOff)) ∗
  ((img.base + kit.loadFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.loadBoxSize) ∗
  ((img.base + kit.loadFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
  ((img.base + kit.loadFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + kit.loadPollOff)) ∗
  ((img.base + ikit.trustFutVtOff) ↦₆₄ᵣ (img.base + ikit.trustFutDropOff)) ∗
  ((img.base + ikit.trustFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.trustBoxSize) ∗
  ((img.base + ikit.trustFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
  ((img.base + ikit.trustFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + ikit.trustPollOff))

/-- Introduces `stageP1VtablesAt` onto any satisfied `SepProp` from `SessionOnlyVtablesOk` and
`IdentityVtablesOk` under `img.FrozenLoaded s`. -/
theorem satisfies_stageP1VtablesAt {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {ikit : IdentityStoreSpec A img.base}
    (hsess : MessageDecrypt.SessionOnlyVtablesOk img kit)
    (hid : IdentityVtablesOk img ikit)
    {s : State} {P : SepProp} (hF : img.FrozenLoaded s) (hP : s.mem ⊨ P) :
    s.mem ⊨ stageP1VtablesAt img kit ikit ∗ P := by
  have h10 := hid.trustFutPoll hF hP
  have h9 := hid.trustFutAlign hF h10
  have h8 := hid.trustFutSize hF h9
  have h7 := hid.trustFutDrop hF h8
  have h6 := hsess.loadFutPoll hF h7
  have h5 := hsess.loadFutAlign hF h6
  have h4 := hsess.loadFutSize hF h5
  have h3 := hsess.loadFutDrop hF h4
  have h2 := hid.trustSlot hF h3
  have h1 := hsess.loadSlot hF h2
  dsimp only [stageP1VtablesAt]
  simpa only [sepConj_assoc] using h1

/-! ## Concrete `KitOk` Discharges at `cliKitStk B` and `cliExterns W` -/

/-- `SessionOnlyKitOkSE` for `cliPollSessKit` at `E2E.HooksE.A0` and `cliExterns W` given `hDeser`. -/
theorem cliPollSess_kitOkSE_of_deser (W : CliHooks) {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img)
    (F0 : FsFiles) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (peer : AddrGhost) (B : RunBudgets)
    (hDeser : subroutine_ok (tripleRatchetProgAtExt img.base (cliExterns W))
      ((tripleRatchetProgAtExt img.base (cliExterns W)).fnAddr recordDeserializeName)
      (sessDeserializeSpec Scope E2E.HooksE.A0 img)) :
    MessageDecrypt.SessionOnlyKitOkSE
      (cliPollSessKit E2E.HooksE.A0 img.base F0 Scope peer (cliKitStk B))
      Scope E2E.Record.encodeRecord (cliExterns W) :=
  SessKit.cliSessKitOkSE_cli W (readStk := B.readFile) himg hDeser
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)

/-- `IdentityStoreKitOkIE` for `cliPollIdKit` at `E2E.HooksE.A0` and `cliExterns W`. -/
theorem cliPollId_kitOkIE (W : CliHooks) {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img)
    (F0 : FsFiles) (peer : AddrGhost) (B : RunBudgets) :
    StoreKit.Identity.IdentityStoreKitOkIE img
      (cliPollIdKit E2E.HooksE.A0 img.base F0 peer (cliKitStk B))
      (cliExterns W) :=
  cliIdKitOkIE_cli_full W (readStk := B.readFile) himg
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)

/-- `PreKeyStoreKitOkImgE` for `cliPollPkKit` at `E2E.HooksE.A0` and `cliExterns W`. -/
theorem cliPollPk_kitOkImgE (W : CliHooks) {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img)
    (F0 : FsFiles) (pid : BitVec 32) (B : RunBudgets) :
    PreKeyStoreKitOkImgE img
      (cliPollPkKit E2E.HooksE.A0 img.base F0 pid (cliKitStk B))
      (cliExterns W) :=
  cliPreKeyKitOk_ext W (readStk := B.readFile) himg
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)

/-- `SignedPreKeyStoreKitOkImgE` for `cliPollSpkKit` at `E2E.HooksE.A0` and `cliExterns W`. -/
theorem cliPollSpk_kitOkImgE (W : CliHooks) {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img)
    (F0 : FsFiles) (sid : BitVec 32) (B : RunBudgets) :
    SignedPreKeyStoreKitOkImgE img
      (cliPollSpkKit E2E.HooksE.A0 img.base F0 sid (cliKitStk B))
      (cliExterns W) :=
  cliSignedPreKeyKitOk_ext W (readStk := B.readFile) himg
    (Nat.le_refl _) (Nat.le_refl _)

/-- `KyberPreKeyStoreKitOkImgE` for `cliPollKpkKit` at `E2E.HooksE.A0` and `cliExterns W`. -/
theorem cliPollKpk_kitOkImgE (W : CliHooks) {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img)
    (F0 : FsFiles) (kid sid : BitVec 32) (kbk : PublicKey) (B : RunBudgets) :
    KyberPreKeyStoreKitOkImgE img
      (cliPollKpkKit E2E.HooksE.A0 img.base F0 kid sid kbk (cliKitStk B))
      (cliExterns W) :=
  cliKyberKitOk_ext W (readStk := B.readFile) himg
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)

/-- Connects `(cliPollSessKit … Slots.scopeKit …).loadRel StoresGhost.opened.sessions peer.val (.ok opt)`
to `Slots.loadRec Scope F0 peer.val =.ok opt`. -/
theorem loadRec_of_cliPollSess_loadRel {A : RustAlloc} {b : BitVec 64}
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

/-- `FsAt` at `tripleRatchetProgAtExt img.base (cliExterns W)` for Stage P1 (`cliPollSessKit` +
`cliPollIdKit`) whenever `s.fs.files = F0`. -/
theorem cliPollStageP1_fsAt {img : Obj.Image} {W : CliHooks}
    (hh : RunSkeleton.RunHooks img E2E.HooksE.A0 (cliExterns W))
    (F0 : FsFiles) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (peer : AddrGhost) (B : RunBudgets) {s : State} (hf : s.fs.files = F0) :
    FsAt
      (fun F => (cliPollSessKit E2E.HooksE.A0 img.base F0 Scope peer (cliKitStk B)).envOk F ∧
                (cliPollIdKit E2E.HooksE.A0 img.base F0 peer (cliKitStk B)).envOk F)
      ((cliPollSessKit E2E.HooksE.A0 img.base F0 Scope peer (cliKitStk B)).Quiet ∧
       (cliPollIdKit E2E.HooksE.A0 img.base F0 peer (cliKitStk B)).Quiet)
      (tripleRatchetProgAtExt img.base (cliExterns W)) s :=
  .inr ⟨⟨cliPollSess_quiet img.base F0 Scope peer (cliKitStk B),
         cliPollId_quiet F0 peer (cliKitStk B)⟩, hh.fs, ⟨hf, hf⟩⟩

private theorem idKeyPairPoll_of_storeDefs {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} {stk : Nat}
    (h : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr Initiate.StoreDefs.idKeyPairPollName)
      (Initiate.StoreDefs.idKeyPairPollSpec cliIo.rd cliWrOk A img stk)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr Initiate.idKeyPairPollName)
      (Initiate.idKeyPairPollSpec cliIo.rd cliWrOk A img stk) :=
  subroutine_ok_map_panic h fun x R _ hpre =>
    ⟨⟨x.fut, x.out, x.self, x.own⟩, R, hpre, fun _ hp => hp, fun _ hp => hp⟩

private theorem idRegIdPoll_of_storeDefs {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} {stk : Nat}
    (h : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr Initiate.StoreDefs.idRegIdPollName)
      (Initiate.StoreDefs.idRegIdPollSpec cliIo.rd cliWrOk A img stk)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr Initiate.idRegIdPollName)
      (Initiate.idRegIdPollSpec cliIo.rd cliWrOk A img stk) :=
  subroutine_ok_map_panic h fun x R _ hpre =>
    ⟨⟨x.fut, x.out, x.self, x.own⟩, R, hpre, fun _ hp => hp, fun _ hp => hp⟩

/-- `IdentitySelfStoreKitOkI` for `cliPollIdKit` + `cliPollSelfKit` at `E2E.HooksE.A0` and
`cliExterns W` given `RunHooks` and `hRead`. -/
theorem cliPollSelf_kitOkI (W : CliHooks) {img : Obj.Image}
    (B : RunBudgets)
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunSkeleton.RunHooks img E2E.HooksE.A0 (cliExterns W))
    (hRead : subroutine_ok (tripleRatchetProgAtExt img.base (cliExterns W))
      ((tripleRatchetProgAtExt img.base (cliExterns W)).fnAddr Cli.readFileName)
      (readFileSpec cliIo.rd cliWrOk E2E.HooksE.A0 img B.readFile))
    (F0 : FsFiles) (peer : AddrGhost) :
    StoreKit.IdentitySelf.IdentitySelfStoreKitOkI img
      (cliPollIdKit E2E.HooksE.A0 img.base F0 peer (cliKitStk B))
      (cliPollSelfKit E2E.HooksE.A0 img.base F0 peer (cliKitStk B))
      (cliExterns W) := by
  have hBase := RunSkeleton.base_aligned himg
  have hGet := Initiate.dirGet_cli_ok W B himg hh hRead
  exact cliSelfKitOkI_of_hops
    (Initiate.StoreCalleesProofs.idOwnShim_lift_stk
      (Initiate.StoreCalleesProofs.idKeyPairShim_fixed_ok hh.alloc hBase) (Nat.le_refl _))
    (idKeyPairPoll_of_storeDefs
      (Initiate.IdKeyPairPoll.idKeyPairPoll_ok_of_deps (stk := (cliKitStk B).kpPoll)
        himg hh.alloc hGet
        (Initiate.identityKeyPairTryFrom_cli_ok W.C himg hh.alloc)
        (by dsimp [cliKitStk, Initiate.IdKeyPairPoll.kpCalleeStk]; omega) hBase))
    (Initiate.StoreCalleesProofs.idOwnShim_lift_stk
      (Initiate.StoreCalleesProofs.idRegIdShim_fixed_ok hh.alloc hBase) (Nat.le_refl _))
    (idRegIdPoll_of_storeDefs
      (Initiate.IdRegIdPoll.idRegIdPoll_ok_of_deps (stk := (cliKitStk B).regIdPoll)
        himg hh.alloc hGet
        (by dsimp [cliKitStk, Initiate.IdRegIdPoll.regCalleeStk]; omega) hBase))
    cliIdFutDrop_ok_ext

/-- `FsAt` at `tripleRatchetProgAtExt img.base (cliExterns W)` for Stage P4 (`stageP4EnvOk` /
`stageP4Quiet` across session, identity, pre-key, and Kyber stores) whenever `s.fs.files = F0`. -/
theorem cliPollStageP4_fsAt {img : Obj.Image} {W : CliHooks}
    (hh : RunSkeleton.RunHooks img E2E.HooksE.A0 (cliExterns W))
    (F0 : FsFiles) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (peer : AddrGhost) (pid sid kid : BitVec 32) (kbk : PublicKey)
    (B : RunBudgets) {s : State} (hf : s.fs.files = F0) :
    FsAt
      (Cli.E2E.Pqxdh.ResponderClosure.Kits.stageP4EnvOk
        (cliPollSessKit E2E.HooksE.A0 img.base F0 Scope peer (cliKitStk B))
        (cliPollIdKit E2E.HooksE.A0 img.base F0 peer (cliKitStk B))
        (cliPollPkKit E2E.HooksE.A0 img.base F0 pid (cliKitStk B))
        (cliPollKpkKit E2E.HooksE.A0 img.base F0 kid sid kbk (cliKitStk B)))
      (Cli.E2E.Pqxdh.ResponderClosure.Kits.stageP4Quiet
        (cliPollSessKit E2E.HooksE.A0 img.base F0 Scope peer (cliKitStk B))
        (cliPollIdKit E2E.HooksE.A0 img.base F0 peer (cliKitStk B))
        (cliPollPkKit E2E.HooksE.A0 img.base F0 pid (cliKitStk B))
        (cliPollKpkKit E2E.HooksE.A0 img.base F0 kid sid kbk (cliKitStk B)))
      (tripleRatchetProgAtExt img.base (cliExterns W)) s :=
  .inr ⟨⟨cliPollSess_quiet img.base F0 Scope peer (cliKitStk B),
         cliPollId_quiet F0 peer (cliKitStk B),
         cliPollPk_quiet img.base F0 pid (cliKitStk B),
         cliPollKpk_quiet img.base F0 kid sid kbk (cliKitStk B)⟩,
        hh.fs, ⟨hf, hf, hf, hf⟩⟩

/-- `FsAt` at `tripleRatchetProgAtExt img.base (cliExterns W)` for Stage P4 Kyber-refusal
(`ikit` + `kpkKit`) whenever `s.fs.files = F0`. -/
theorem cliPollStageP4Refused_fsAt {img : Obj.Image} {W : CliHooks}
    (hh : RunSkeleton.RunHooks img E2E.HooksE.A0 (cliExterns W))
    (F0 : FsFiles) (peer : AddrGhost) (kid sid : BitVec 32) (kbk : PublicKey)
    (B : RunBudgets) {s : State} (hf : s.fs.files = F0) :
    FsAt
      (fun F => (cliPollIdKit E2E.HooksE.A0 img.base F0 peer (cliKitStk B)).envOk F ∧
                (cliPollKpkKit E2E.HooksE.A0 img.base F0 kid sid kbk (cliKitStk B)).envOk F)
      ((cliPollIdKit E2E.HooksE.A0 img.base F0 peer (cliKitStk B)).Quiet ∧
       (cliPollKpkKit E2E.HooksE.A0 img.base F0 kid sid kbk (cliKitStk B)).Quiet)
      (tripleRatchetProgAtExt img.base (cliExterns W)) s :=
  .inr ⟨⟨cliPollId_quiet F0 peer (cliKitStk B),
         cliPollKpk_quiet img.base F0 kid sid kbk (cliKitStk B)⟩,
        hh.fs, ⟨hf, hf⟩⟩

/-! ## `Ext` / `RunHooksExt` Poll Kit & `FsAt` Discharges -/

/-- `SessionOnlyKitOkSE` for `cliPollSessKit` at `A` and `cliExternsWith ext` given
`CliExternsOk P A ext` and `hDeser` (`sessDeserializeSpec`). -/
theorem cliPollSess_kitOkSE_of_deser_ext {P : E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P A ext)
    {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    (F0 : FsFiles) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (peer : AddrGhost) (B : RunBudgets)
    (hDeser : subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr recordDeserializeName)
      (sessDeserializeSpec Scope A img))
    (hreadStk : extHookStack ≤ B.readFile := by decide) :
    MessageDecrypt.SessionOnlyKitOkSE
      (cliPollSessKit A img.base F0 Scope peer (cliKitStk B))
      Scope E2E.Record.encodeRecord (cliExternsWith ext) :=
  SessKit.cliSessKitOkSE_ext_noPool hOk (readStk := B.readFile) himg hDeser
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) hreadStk

/-- `SessionOnlyKitOkSE` for `cliPollSessKit` at `A` and `cliExternsWith ext` given
`CliExternsOk P A ext` and `hDeser` (`sessDeserializeExtSpec`). -/
theorem cliPollSess_kitOkSE_of_deserExt {P : E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P A ext)
    {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    (F0 : FsFiles) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (peer : AddrGhost) (B : RunBudgets)
    (hDeser : subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr recordDeserializeName)
      (sessDeserializeExtSpec Scope A img))
    (hreadStk : extHookStack ≤ B.readFile := by decide) :
    MessageDecrypt.SessionOnlyKitOkSE
      (cliPollSessKit A img.base F0 Scope peer (cliKitStk B))
      Scope E2E.Record.encodeRecord (cliExternsWith ext) :=
  SessKit.cliSessKitOkSE_ext hOk (readStk := B.readFile) himg hDeser
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) hreadStk

/-- `SessionOnlyKitOkSE` for `cliPollSessKit` at arbitrary `A` and `ext` given `RunHooksExt`,
`hRead`, `hDeser` (`sessDeserializeExtSpec`), and `hSer`. -/
theorem cliPollSess_kitOkSE_of_hooksExt {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (B : RunBudgets)
    (F0 : FsFiles) (Scope : SessionRecord (List (BitVec 8)) → Prop) (peer : AddrGhost)
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunSkeleton.RunHooksExt img A ext)
    (hRead : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr Cli.readFileName)
      (readFileSpec cliIo.rd cliWrOk A img B.readFile))
    (hDeser : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr recordDeserializeName)
      (sessDeserializeExtSpec Scope A img))
    (hSer : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr recordSerializeName)
      ((Proofs.libsignal.Hooks2.serializeCanonSpecX A).inImage img)) :
    MessageDecrypt.SessionOnlyKitOkSE
      (cliPollSessKit A img.base F0 Scope peer (cliKitStk B))
      Scope E2E.Record.encodeRecord ext :=
  SessKit.cliSessKitOkSE_ext_of_hooks (readStk := B.readFile) himg hh hRead hDeser hSer
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)

/-- `IdentityStoreKitOkIE` for `cliPollIdKit` at `A` and `cliExternsWith ext` given
`CliExternsOk P A ext`. -/
theorem cliPollId_kitOkIE_ext {P : E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P A ext)
    {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    (F0 : FsFiles) (peer : AddrGhost) (B : RunBudgets)
    (hreadStk : extHookStack ≤ B.readFile := by decide) :
    StoreKit.Identity.IdentityStoreKitOkIE img
      (cliPollIdKit A img.base F0 peer (cliKitStk B))
      (cliExternsWith ext) :=
  cliIdKitOkIE_ext_of_externsOk_full hOk (readStk := B.readFile) himg
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) hreadStk

/-- `IdentityStoreKitOkIE` for `cliPollIdKit` at arbitrary `A` and `ext` given `RunHooksExt`,
`hRead`, and `PublicKeyEqOkExt32`. -/
theorem cliPollId_kitOkIE_of_hooksExt {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (B : RunBudgets)
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunSkeleton.RunHooksExt img A ext)
    (hRead : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr Cli.readFileName)
      (readFileSpec cliIo.rd cliWrOk A img B.readFile))
    (hEq : Getters.PublicKeyEqOkExt32 img.base ext)
    (F0 : FsFiles) (peer : AddrGhost) :
    StoreKit.Identity.IdentityStoreKitOkIE img
      (cliPollIdKit A img.base F0 peer (cliKitStk B)) ext :=
  cliIdKitOkIE_ext32_full (readStk := B.readFile) himg hh hRead hEq
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)

/-- `PreKeyStoreKitOkImgE` for `cliPollPkKit` at arbitrary `A` and `ext` given `RunHooksExt`
and `hRead`. -/
theorem cliPollPk_kitOkImgE_ext (C : Crypto) {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (B : RunBudgets)
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunSkeleton.RunHooksExt img A ext)
    (hRead : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr Cli.readFileName)
      (readFileSpec cliIo.rd cliWrOk A img B.readFile))
    (F0 : FsFiles) (pid : BitVec 32) :
    PreKeyStoreKitOkImgE img
      (cliPollPkKit A img.base F0 pid (cliKitStk B)) ext :=
  cliPreKeyKitOk_of_hooksExt C (readStk := B.readFile) himg hh hRead
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)

/-- `SignedPreKeyStoreKitOkImgE` for `cliPollSpkKit` at arbitrary `A` and `ext` given `RunHooksExt`
and `hRead`. -/
theorem cliPollSpk_kitOkImgE_ext {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (B : RunBudgets)
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunSkeleton.RunHooksExt img A ext)
    (hRead : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr Cli.readFileName)
      (readFileSpec cliIo.rd cliWrOk A img B.readFile))
    (F0 : FsFiles) (sid : BitVec 32) :
    SignedPreKeyStoreKitOkImgE img
      (cliPollSpkKit A img.base F0 sid (cliKitStk B)) ext :=
  cliSignedPreKeyKitOk_of_hooksExt (readStk := B.readFile) himg hh hRead
    (Nat.le_refl _) (Nat.le_refl _)

/-- `KyberPreKeyStoreKitOkImgE` for `cliPollKpkKit` at arbitrary `A` and `ext` given `RunHooksExt`
and `hRead`. -/
theorem cliPollKpk_kitOkImgE_ext {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (B : RunBudgets)
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunSkeleton.RunHooksExt img A ext)
    (hRead : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr Cli.readFileName)
      (readFileSpec cliIo.rd cliWrOk A img B.readFile))
    (F0 : FsFiles) (kid sid : BitVec 32) (kbk : PublicKey) :
    KyberPreKeyStoreKitOkImgE img
      (cliPollKpkKit A img.base F0 kid sid kbk (cliKitStk B)) ext :=
  cliKyberKitOk_of_hooksExt (readStk := B.readFile) himg hh hRead
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)

/-- `IdentitySelfStoreKitOkI` for `cliPollIdKit` + `cliPollSelfKit` at arbitrary `A` and `ext`
given `RunHooksExt` and `hRead`. -/
theorem cliPollSelf_kitOkI_ext (C : Crypto) {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (B : RunBudgets)
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunSkeleton.RunHooksExt img A ext)
    (hRead : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr Cli.readFileName)
      (readFileSpec cliIo.rd cliWrOk A img B.readFile))
    (F0 : FsFiles) (peer : AddrGhost) :
    StoreKit.IdentitySelf.IdentitySelfStoreKitOkI img
      (cliPollIdKit A img.base F0 peer (cliKitStk B))
      (cliPollSelfKit A img.base F0 peer (cliKitStk B)) ext := by
  have hBase := RunSkeleton.base_aligned himg
  have hGet := Initiate.dirGet_ext_ok B himg hh hRead
  exact cliSelfKitOkI_of_hops
    (Initiate.StoreCalleesProofs.idOwnShim_lift_stk
      (Initiate.StoreCalleesProofs.idKeyPairShim_fixed_ok hh.alloc hBase) (Nat.le_refl _))
    (idKeyPairPoll_of_storeDefs
      (Initiate.IdKeyPairPoll.idKeyPairPoll_ok_of_deps (stk := (cliKitStk B).kpPoll)
        himg hh.alloc hGet
        (Initiate.identityKeyPairTryFrom_cli_ok C himg hh.alloc)
        (by dsimp [cliKitStk, Initiate.IdKeyPairPoll.kpCalleeStk]; omega) hBase))
    (Initiate.StoreCalleesProofs.idOwnShim_lift_stk
      (Initiate.StoreCalleesProofs.idRegIdShim_fixed_ok hh.alloc hBase) (Nat.le_refl _))
    (idRegIdPoll_of_storeDefs
      (Initiate.IdRegIdPoll.idRegIdPoll_ok_of_deps (stk := (cliKitStk B).regIdPoll)
        himg hh.alloc hGet
        (by dsimp [cliKitStk, Initiate.IdRegIdPoll.regCalleeStk]; omega) hBase))
    cliIdFutDrop_ok_ext

/-- `FsAt` at `tripleRatchetProgAtExt img.base ext` for Stage P1 (`cliPollSessKit` + `cliPollIdKit`)
from `RunHooksExt` whenever `s.fs.files = F0`. -/
theorem cliPollStageP1_fsAt_of_hooksExt {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hh : RunSkeleton.RunHooksExt img A ext)
    (F0 : FsFiles) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (peer : AddrGhost) (B : RunBudgets) {s : State} (hf : s.fs.files = F0) :
    FsAt
      (fun F => (cliPollSessKit A img.base F0 Scope peer (cliKitStk B)).envOk F ∧
                (cliPollIdKit A img.base F0 peer (cliKitStk B)).envOk F)
      ((cliPollSessKit A img.base F0 Scope peer (cliKitStk B)).Quiet ∧
       (cliPollIdKit A img.base F0 peer (cliKitStk B)).Quiet)
      (tripleRatchetProgAtExt img.base ext) s :=
  .inr ⟨⟨cliPollSess_quiet img.base F0 Scope peer (cliKitStk B),
         cliPollId_quiet F0 peer (cliKitStk B)⟩, hh.fs, ⟨hf, hf⟩⟩

/-- `FsAt` at `tripleRatchetProgAtExt img.base ext` for Stage P4 (`stageP4EnvOk` /
`stageP4Quiet` across session, identity, pre-key, and Kyber stores) whenever `s.fs.files = F0`. -/
theorem cliPollStageP4_fsAt_ext {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hh : RunSkeleton.RunHooksExt img A ext)
    (F0 : FsFiles) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (peer : AddrGhost) (pid sid kid : BitVec 32) (kbk : PublicKey)
    (B : RunBudgets) {s : State} (hf : s.fs.files = F0) :
    FsAt
      (Cli.E2E.Pqxdh.ResponderClosure.Kits.stageP4EnvOk
        (cliPollSessKit A img.base F0 Scope peer (cliKitStk B))
        (cliPollIdKit A img.base F0 peer (cliKitStk B))
        (cliPollPkKit A img.base F0 pid (cliKitStk B))
        (cliPollKpkKit A img.base F0 kid sid kbk (cliKitStk B)))
      (Cli.E2E.Pqxdh.ResponderClosure.Kits.stageP4Quiet
        (cliPollSessKit A img.base F0 Scope peer (cliKitStk B))
        (cliPollIdKit A img.base F0 peer (cliKitStk B))
        (cliPollPkKit A img.base F0 pid (cliKitStk B))
        (cliPollKpkKit A img.base F0 kid sid kbk (cliKitStk B)))
      (tripleRatchetProgAtExt img.base ext) s :=
  .inr ⟨⟨cliPollSess_quiet img.base F0 Scope peer (cliKitStk B),
         cliPollId_quiet F0 peer (cliKitStk B),
         cliPollPk_quiet img.base F0 pid (cliKitStk B),
         cliPollKpk_quiet img.base F0 kid sid kbk (cliKitStk B)⟩,
        hh.fs, ⟨hf, hf, hf, hf⟩⟩

/-- `FsAt` at `tripleRatchetProgAtExt img.base ext` for Stage P4 Kyber-refusal
(`ikit` + `kpkKit`) from `RunHooksExt` whenever `s.fs.files = F0`. -/
theorem cliPollStageP4Refused_fsAt_ext {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hh : RunSkeleton.RunHooksExt img A ext)
    (F0 : FsFiles) (peer : AddrGhost) (kid sid : BitVec 32) (kbk : PublicKey)
    (B : RunBudgets) {s : State} (hf : s.fs.files = F0) :
    FsAt
      (fun F => (cliPollIdKit A img.base F0 peer (cliKitStk B)).envOk F ∧
                (cliPollKpkKit A img.base F0 kid sid kbk (cliKitStk B)).envOk F)
      ((cliPollIdKit A img.base F0 peer (cliKitStk B)).Quiet ∧
       (cliPollKpkKit A img.base F0 kid sid kbk (cliKitStk B)).Quiet)
      (tripleRatchetProgAtExt img.base ext) s :=
  .inr ⟨⟨cliPollId_quiet F0 peer (cliKitStk B),
         cliPollKpk_quiet img.base F0 kid sid kbk (cliKitStk B)⟩,
        hh.fs, ⟨hf, hf⟩⟩

end CryptoVerification.SignalSession.Cli.RunProofs.Poll
