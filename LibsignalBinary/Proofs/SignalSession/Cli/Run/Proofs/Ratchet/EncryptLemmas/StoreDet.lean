/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.LoadRec
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ScopeIn
import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSessionApiFacts
public import LibsignalBinary.Proofs.SpecLemmas.LibsignalE2E.PqxdhCorrectModelProofDefs

/-!
# Store-Answer Determinism and Scope Lifting for `encrypt`

Establishes `Scope ⊆ Slots.scopeIn ⊆ Slots.scopeKit` invariance for `Slots.loadRec` and
`w1CliAnswers`, connects `encOk₀` to the kit coin/empty disjunction, and proves
`cliEncrypt_store_det` along `encryptFlat`.
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
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.KitInst
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity

/-! ## Mirrors of `encrypt` store and model definitions -/

noncomputable abbrev w1CliAnswers (Scope : SessionRecord (List (BitVec 8)) → Prop) (F : FsFiles)
    (peer : AddrVal) (k : Option IdentityKey) : StoreAnswers (List (BitVec 8)) Unit where
  loadSession := Slots.loadRec Scope F peer
  isTrustedIdentity := match k with
    | some k => StoresGhost.opened.identity.trusted cliIo.rd F peer k
    | none => .ok false
  saveIdentity := match k with
    | some k => StoresGhost.opened.identity.saveAns cliIo.rd F peer k
    | none => .ok .newOrUnchanged
  storeSession := .ok ()

abbrev w1CliStep (F : FsFiles) (g : StoresGhost) : StoreCall AddrVal (List (BitVec 8)) → StoresGhost
  | .saveIdentity rem k => { g with identity := g.identity.saveUpd cliIo.rd F rem k }
  | .storeSession rem r =>
    { g with sessions := g.sessions.put (Cli.addressText rem) (E2E.Record.encodeRecord r) }
  | _ => g

abbrev w1CliFinal (F : FsFiles) (calls : List (StoreCall AddrVal (List (BitVec 8)))) : StoresGhost :=
  calls.foldl (w1CliStep F) StoresGhost.opened

noncomputable abbrev w1EncKey (Scope : SessionRecord (List (BitVec 8)) → Prop) (F : FsFiles)
    (peer : AddrVal) : Option IdentityKey :=
  match Slots.loadRec Scope F peer with
  | .ok (some r) =>
    match r.currentSession with
    | some s =>
      match execOk OutgoingTripleRatchet.fromSessionState s.state with
      | .ok (_, taken) => taken.remoteIdentity
      | .error _ => none
    | none => none
  | _ => none

noncomputable abbrev w1EncDef (W : PEParams) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (F : FsFiles) (peer me : AddrVal) (ptext coins : List (BitVec 8)) :
    SlotAns CiphertextMessage :=
  match LibsignalSessionApi.messageEncrypt W.C protoSignalCodec (pqxdhSpqrModel W).spqr
      (serializeAddrVals (serviceIdParse uuidTryParse)) (w1CliAnswers Scope F peer (w1EncKey Scope F peer))
      ptext peer me unixEpoch coins with
  | (.ok m, calls) => some (some (w1CliFinal F calls, m))
  | (.error .panic, _) => none
  | (.error _, _) => some none

theorem w1EncDef_eq_model (W : PEParams) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (F : FsFiles) (x : CryptoVerification.LibsignalPublicApi.EncryptGhost)
    (hnow : x.now = unixEpoch) :
    w1EncDef W Scope F x.rem.val x.loc.val x.ptext x.rest =
      match x.model W.C (pqxdhSpqrModel W) uuidTryParse
          (w1CliAnswers Scope F x.rem.val (w1EncKey Scope F x.rem.val)) with
      | (.ok m, calls) => some (some (w1CliFinal F calls, m))
      | (.error .panic, _) => none
      | (.error _, _) => some none := by
  simp only [w1EncDef, CryptoVerification.LibsignalPublicApi.EncryptGhost.model, hnow]

abbrev w1EncryptNeed (B : RunBudgets) : Nat :=
  2 ^ 20 + B.readFile

/-! ## Scope lifting (`Scope → Slots.scopeIn → Slots.scopeKit`) -/

theorem scopeKit_of_sub {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hsub : ∀ r, Scope r → Slots.scopeIn r) (r : SessionRecord (List (BitVec 8)))
    (hr : Scope r) : Slots.scopeKit r :=
  Slots.scopeKit_of_scopeIn (hsub r hr)

theorem sessFileWf_mono {S₁ S₂ : SessionRecord (List (BitVec 8)) → Prop}
    (h : ∀ r, S₁ r → S₂ r) {bs : List (BitVec 8)} (hwf : SessFileWf S₁ bs) :
    SessFileWf S₂ bs := by
  rcases hwf with rfl | ⟨r, hr_enc, hr_sc⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨r, hr_enc, h r hr_sc⟩

theorem sessLoadAns_mono {S₁ S₂ : SessionRecord (List (BitVec 8)) → Prop}
    (h : ∀ r, S₁ r → S₂ r) {res : Except Unit (List (BitVec 8))}
    {ans : Except Unit (Option (SessionRecord (List (BitVec 8))))}
    (hla : SessLoadAns S₁ res ans) : SessLoadAns S₂ res ans := by
  rcases res with _ | (_ | ⟨b, bs⟩)
  · exact hla
  · exact hla
  · obtain ⟨r, hans, henc, hsc⟩ := hla
    exact ⟨r, hans, henc, h r hsc⟩

theorem filesOkPeer_mono {S₁ S₂ : SessionRecord (List (BitVec 8)) → Prop}
    (h : ∀ r, S₁ r → S₂ r) {F : FsFiles} {peer : AddrVal}
    (hok : Slots.FilesOkPeer S₁ F peer) : Slots.FilesOkPeer S₂ F peer where
  nameLt := hok.nameLt
  textLt := hok.textLt
  sessPathOk := hok.sessPathOk
  idPathOk := hok.idPathOk
  sessPathLt := hok.sessPathLt
  idPathLt := hok.idPathLt
  sessGet := let ⟨bs, hbs, hwf⟩ := hok.sessGet; ⟨bs, hbs, sessFileWf_mono h hwf⟩
  idGet := hok.idGet

/-- Scope invariance of `Slots.loadRec` between `Scope` and `Slots.scopeKit` under `FilesOkPeer Scope` and `EncodeInjOn Slots.scopeKit`. -/
theorem loadRec_scopeKit_eq {Scope : SessionRecord (List (BitVec 8)) → Prop} {F : FsFiles}
    {peer : AddrVal} (hinjK : Slots.EncodeInjOn Slots.scopeKit)
    (hsub : ∀ r, Scope r → Slots.scopeIn r)
    (hok : Slots.FilesOkPeer Scope F peer) :
    Slots.loadRec Slots.scopeKit F peer = Slots.loadRec Scope F peer := by
  symm
  exact Slots.loadRec_unique hinjK
    (sessLoadAns_mono (scopeKit_of_sub hsub) (Slots.sessLoadAns_loadRec hok))

theorem encKey_scopeKit_eq {Scope : SessionRecord (List (BitVec 8)) → Prop} {F : FsFiles}
    {peer : AddrVal} (hinjK : Slots.EncodeInjOn Slots.scopeKit)
    (hsub : ∀ r, Scope r → Slots.scopeIn r)
    (hok : Slots.FilesOkPeer Scope F peer) :
    w1EncKey Slots.scopeKit F peer = w1EncKey Scope F peer := by
  simp only [w1EncKey, loadRec_scopeKit_eq hinjK hsub hok]

theorem cliAnswers_scopeKit_eq {Scope : SessionRecord (List (BitVec 8)) → Prop} {F : FsFiles}
    {peer : AddrVal} {k : Option IdentityKey} (hinjK : Slots.EncodeInjOn Slots.scopeKit)
    (hsub : ∀ r, Scope r → Slots.scopeIn r)
    (hok : Slots.FilesOkPeer Scope F peer) :
    w1CliAnswers Slots.scopeKit F peer k = w1CliAnswers Scope F peer k := by
  simp only [w1CliAnswers, loadRec_scopeKit_eq hinjK hsub hok]

theorem encDef_scopeKit_eq (W : PEParams) {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {peer me : AddrVal} {ptext coins : List (BitVec 8)}
    (hinjK : Slots.EncodeInjOn Slots.scopeKit)
    (hsub : ∀ r, Scope r → Slots.scopeIn r)
    (hok : Slots.FilesOkPeer Scope F peer) :
    w1EncDef W Slots.scopeKit F peer me ptext coins = w1EncDef W Scope F peer me ptext coins := by
  simp only [w1EncDef, encKey_scopeKit_eq hinjK hsub hok, cliAnswers_scopeKit_eq hinjK hsub hok]

/-! ## `encOk₀` disjunction and `loadRel` uniqueness -/

/-- Any `loadRel` answer of `cliSessionStoreSpec` at `Slots.scopeKit` on `StoresGhost.opened` equals `Slots.loadRec Scope F rem` when `rem = peer.val`. -/
theorem cliSessLoadRel_eq_loadRec_scope {A : RustAlloc} {b : BitVec 64}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {F : FsFiles} {peer : AddrGhost}
    {s1 s2 s3 s4 : Nat} {rem : AddrVal}
    {ans : Except Unit (Option (SessionRecord (List (BitVec 8))))}
    (hinjK : Slots.EncodeInjOn Slots.scopeKit)
    (hsub : ∀ r, Scope r → Slots.scopeIn r)
    (hok : Slots.FilesOkPeer Scope F rem)
    (hl : (cliSessionStoreSpec A b cliIo.rd F cliWrOk Slots.scopeKit peer s1 s2 s3 s4).loadRel
      StoresGhost.opened.sessions rem ans) :
    ans = Slots.loadRec Scope F rem := by
  obtain ⟨bs, hbs, hla⟩ := hl
  have hla' : SessLoadAns Slots.scopeKit
      (StoresGhost.opened.sessions.get cliIo.rd F (Cli.addressText rem)) ans := by
    rwa [hbs]
  rw [← loadRec_scopeKit_eq hinjK hsub hok]
  exact Slots.loadRec_unique hinjK hla'

theorem loadRec_ne_error {Scope : SessionRecord (List (BitVec 8)) → Prop} {F : FsFiles}
    {peer : AddrVal} (hok : Slots.FilesOkPeer Scope F peer) :
    Slots.loadRec Scope F peer ≠ .error () := by
  have hla := Slots.sessLoadAns_loadRec hok
  obtain ⟨bs, hbs, _⟩ := hok.sessGet
  rw [hbs] at hla
  intro herr
  rw [herr] at hla
  rcases bs with _ | ⟨b, bs'⟩
  · cases hla
  · obtain ⟨_, hans, _, _⟩ := hla
    cases hans

/-- Derives the entry coin-length or empty-PQ disjunction from `Slots.encOk₀`. -/
theorem encOk₀_to_kitScopeAt {A : RustAlloc} {b : BitVec 64}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {F : FsFiles} {peer : AddrGhost}
    {coins : List (BitVec 8)} {s1 s2 s3 s4 : Nat}
    (hinjK : Slots.EncodeInjOn Slots.scopeKit)
    (hsub : ∀ r, Scope r → Slots.scopeIn r)
    (hok : Slots.FilesOkPeer Scope F peer.val)
    (henc : Slots.encOk₀ Scope F peer.val coins) :
    64 ≤ coins.length ∨
      ∀ r, (cliSessionStoreSpec A b cliIo.rd F cliWrOk Slots.scopeKit peer s1 s2 s3 s4).ScopeAt
        Slots.scopeKit StoresGhost.opened.sessions peer.val r →
        E2E.Record.RecordPqEmpty r := by
  by_cases h64 : 64 ≤ coins.length
  · exact Or.inl h64
  · refine Or.inr fun r hSc => ?_
    have hlr : Slots.loadRec Scope F peer.val = .ok (some r) :=
      (cliSessLoadRel_eq_loadRec_scope hinjK hsub hok hSc.2).symm
    rcases Slots.loadRec_encOk₀ henc hlr with h64' | hpq
    · exact absurd h64' h64
    · exact hpq

/-! ## Store-answer determinism and `w1CliFinal` -/

theorem cliTraceOfWith_eq_nil {A : RustAlloc} {b : BitVec 64} {F : FsFiles}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {peer : AddrGhost}
    {s1 s2 s3 s4 i1 i2 i3 i4 : Nat}
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (ans : StoreAnswers (List (BitVec 8)) Unit)
    (calls : List (StoreCall AddrVal (List (BitVec 8)))) :
    (cliIdentityStoreSpec A b cliIo.rd F cliWrOk peer i1 i2 i3 i4).traceOfWith
      (cliSessionStoreSpec A b cliIo.rd F cliWrOk Scope peer s1 s2 s3 s4)
      encRecord ans calls = [] := by
  simp only [IdentityStoreSpec.traceOfWith, List.flatMap_eq_nil_iff]
  intro c _
  cases c <;> rfl

def mkCliStores (sess : DirGhost) (idg : IdGhost) : StoresGhost :=
  { StoresGhost.opened with sessions := sess, identity := idg }

private theorem writes_save_store (F : FsFiles) (peer : AddrVal) (k : IdentityKey)
    (r' : SessionRecord (List (BitVec 8))) :
    (w1CliFinal F [.loadSession peer, .isTrustedIdentity peer k .sending,
        .saveIdentity peer k, .storeSession peer r']).writes =
      (StoresGhost.opened.identity.saveUpd cliIo.rd F peer k).peers.writes ++
        [(pathOf (utf8 "sessions") (Cli.addressText peer), E2E.Record.encodeRecord r')] := by
  have hid_own : (StoresGhost.opened.identity.saveUpd cliIo.rd F peer k).own.writes = [] := by
    unfold IdGhost.saveUpd
    split <;> rfl
  have hsess : (StoresGhost.opened.sessions.put (Cli.addressText peer) (E2E.Record.encodeRecord r')).writes =
      [(pathOf (utf8 "sessions") (Cli.addressText peer), E2E.Record.encodeRecord r')] := rfl
  have h1 : StoresGhost.opened.signed.writes = [] := rfl
  have h2 : StoresGhost.opened.kyber.oneTime.writes = [] := rfl
  have h3 : StoresGhost.opened.kyber.lastResort.writes = [] := rfl
  have h4 : StoresGhost.opened.oneTime.writes = [] := rfl
  have h5 : StoresGhost.opened.pub.writes = [] := rfl
  dsimp only [w1CliFinal, List.foldl, w1CliStep, StoresGhost.writes]
  rw [hid_own, hsess, h1, h2, h3, h4, h5]
  simp only [List.nil_append, List.append_nil]

private theorem wrapFlat_ne_store (W : PEParams) (x : EncryptGhost)
    (s : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8))) :
    (wrapFlat (E := Unit) W.C protoSignalCodec (pqxdhSpqrModel W).spqr
      (serializeAddrVals (serviceIdParse uuidTryParse)) x.ptext x.rem.val x.loc.val
      x.now x.rest s otr) ≠ .error (.store ()) := by
  unfold wrapFlat
  rcases s.pendingPreKey with _ | items
  · rcases execOk (OutgoingTripleRatchet.encrypt W.C protoSignalCodec (pqxdhSpqrModel W).spqr
        x.ptext none x.rest) otr with e | ⟨_, _⟩
    · cases e <;> simp [ApiError.ofProtocol]
    · simp
  · dsimp only
    split
    · simp
    · split
      · simp
      · split
        · simp
        · rcases execOk (OutgoingTripleRatchet.encrypt W.C protoSignalCodec (pqxdhSpqrModel W).spqr
              x.ptext (serializeAddrVals (serviceIdParse uuidTryParse) x.loc.val x.rem.val)
              x.rest) otr with e | ⟨_, _⟩
          · cases e <;> simp [ApiError.ofProtocol]
          · simp

/-- Determinism of `EncryptGhost.model` under `kit.callsRel` and `ikit.idCallsRel` at
`StoresGhost.opened`, matching `w1CliAnswers` and `w1CliFinal` and establishing `cliWrOk` on
committed writes. -/
theorem cliEncrypt_store_det {A : RustAlloc} {b : BitVec 64}
    (W : PEParams) {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {s1 s2 s3 s4 i1 i2 i3 i4 : Nat}
    (x : EncryptGhost)
    (answers : StoreAnswers (List (BitVec 8)) Unit)
    (hinjK : Slots.EncodeInjOn Slots.scopeKit)
    (hsub : ∀ r, Scope r → Slots.scopeIn r)
    (hok : Slots.FilesOkPeer Scope F x.rem.val)
    (hcalls : (cliSessionStoreSpec A b cliIo.rd F cliWrOk Slots.scopeKit x.rem s1 s2 s3 s4).callsRel
      StoresGhost.opened.sessions answers (x.model W.C (pqxdhSpqrModel W) uuidTryParse answers).2)
    (hid : (cliIdentityStoreSpec A b cliIo.rd F cliWrOk x.rem i1 i2 i3 i4).idCallsRel
      StoresGhost.opened.identity answers (x.model W.C (pqxdhSpqrModel W) uuidTryParse answers).2) :
    let kit := cliSessionStoreSpec A b cliIo.rd F cliWrOk Slots.scopeKit x.rem s1 s2 s3 s4
    let ikit := cliIdentityStoreSpec A b cliIo.rd F cliWrOk x.rem i1 i2 i3 i4
    let resCalls := x.model W.C (pqxdhSpqrModel W) uuidTryParse answers
    let cliAns := w1CliAnswers Scope F x.rem.val (w1EncKey Scope F x.rem.val)
    resCalls = x.model W.C (pqxdhSpqrModel W) uuidTryParse cliAns ∧
      resCalls.1 ≠ .error (.store ()) ∧
      mkCliStores (kit.storeFinal StoresGhost.opened.sessions answers resCalls.2)
        (ikit.idFinal StoresGhost.opened.identity answers resCalls.2) = w1CliFinal F resCalls.2 ∧
      (∀ v, resCalls.1 = .ok v → ∀ pw ∈ (w1CliFinal F resCalls.2).writes, cliWrOk pw.1) := by
  dsimp only
  set kit := cliSessionStoreSpec A b cliIo.rd F cliWrOk Slots.scopeKit x.rem s1 s2 s3 s4
  set ikit := cliIdentityStoreSpec A b cliIo.rd F cliWrOk x.rem i1 i2 i3 i4
  set cliAns := w1CliAnswers Scope F x.rem.val (w1EncKey Scope F x.rem.val)
  simp only [EncryptGhost.model, messageEncrypt_eq_flat] at hcalls hid ⊢
  have hloadRel : kit.loadRel StoresGhost.opened.sessions x.rem.val answers.loadSession := by
    simp only [encryptFlat] at hcalls
    rcases hl0 : answers.loadSession with _ | (_ | r)
    · simp only [hl0] at hcalls; rw [← hl0]; exact hcalls.1
    · simp only [hl0] at hcalls; rw [← hl0]; exact hcalls.1
    · simp only [hl0] at hcalls
      rcases hc0 : r.currentSession with _ | s
      · simp only [hc0] at hcalls; rw [← hl0]; exact hcalls.1
      · simp only [hc0] at hcalls
        rcases hf0 : execOk OutgoingTripleRatchet.fromSessionState s.state with _ | ⟨otr, taken⟩
        · simp only [hf0] at hcalls; rw [← hl0]; exact hcalls.1
        · simp only [hf0] at hcalls
          rcases hk0 : taken.remoteIdentity with _ | k
          · simp only [hk0] at hcalls; rw [← hl0]; exact hcalls.1
          · simp only [hk0] at hcalls
            rcases hw0 : wrapFlat (E := Unit) W.C protoSignalCodec (pqxdhSpqrModel W).spqr
                  (serializeAddrVals (serviceIdParse uuidTryParse)) x.ptext x.rem.val x.loc.val
                  x.now x.rest s otr with _ | ⟨msg, otr'⟩
            · simp only [hw0] at hcalls; rw [← hl0]; exact hcalls.1
            · simp only [hw0] at hcalls
              rcases ht0 : answers.isTrustedIdentity with _ | (_ | _)
              · simp only [ht0] at hcalls; rw [← hl0]; exact hcalls.1
              · simp only [ht0] at hcalls; rw [← hl0]; exact hcalls.1
              · simp only [ht0] at hcalls
                rcases hs0 : answers.saveIdentity with _ | _
                · simp only [hs0] at hcalls; rw [← hl0]; exact hcalls.1
                · simp only [hs0] at hcalls
                  rcases hst0 : answers.storeSession with _ | ⟨⟩ <;>
                    (simp only [hst0] at hcalls; rw [← hl0]; exact hcalls.1)
  have hload_eq : answers.loadSession = Slots.loadRec Scope F x.rem.val :=
    cliSessLoadRel_eq_loadRec_scope hinjK hsub hok hloadRel
  have hload_cli : cliAns.loadSession = Slots.loadRec Scope F x.rem.val := rfl
  have hload_ne_err : answers.loadSession ≠ .error () :=
    hload_eq ▸ loadRec_ne_error hok
  simp only [encryptFlat] at hcalls hid ⊢
  rcases hl : answers.loadSession with ⟨⟩ | (_ | r)
  · exact absurd hl hload_ne_err
  · have hcl : cliAns.loadSession = .ok none := hload_cli.trans (hload_eq.symm.trans hl)
    simp only [hcl]
    exact ⟨trivial, by simp, rfl, fun _ h => nomatch h⟩
  · have hcl : cliAns.loadSession = .ok (some r) := hload_cli.trans (hload_eq.symm.trans hl)
    simp only [hl, hcl] at hcalls hid ⊢
    rcases hc : r.currentSession with _ | s
    · exact ⟨rfl, by simp, rfl, fun _ h => nomatch h⟩
    · simp only [hc] at hcalls hid ⊢
      rcases hf : execOk OutgoingTripleRatchet.fromSessionState s.state with ef | ⟨otr, taken⟩
      · refine ⟨rfl, ?_, rfl, fun _ h => nomatch h⟩
        cases ef <;> simp [ApiError.ofProtocol]
      · simp only [hf] at hcalls hid ⊢
        rcases hk : taken.remoteIdentity with _ | k
        · exact ⟨rfl, by simp, rfl, fun _ h => nomatch h⟩
        · simp only [hk] at hcalls hid ⊢
          rcases hw : wrapFlat (E := Unit) W.C protoSignalCodec (pqxdhSpqrModel W).spqr
              (serializeAddrVals (serviceIdParse uuidTryParse)) x.ptext x.rem.val x.loc.val
              x.now x.rest s otr with ew | ⟨msg, otr'⟩
          · refine ⟨rfl, ?_, rfl, fun _ h => nomatch h⟩
            intro hew
            exact wrapFlat_ne_store W x s otr (hw.trans (congrArg Except.error (Except.error.inj hew)))
          · simp only [hw] at hcalls hid ⊢
            have hek : w1EncKey Scope F x.rem.val = some k := by
              simp [w1EncKey, ← hload_eq, hl, hc, hf, hk]
            have hcli_tr : cliAns.isTrustedIdentity =
                StoresGhost.opened.identity.trusted cliIo.rd F x.rem.val k := by
              simp [cliAns, hek]
            have hcli_sv : cliAns.saveIdentity =
                StoresGhost.opened.identity.saveAns cliIo.rd F x.rem.val k := by
              simp [cliAns, hek]
            have htrRel : ikit.trustRel StoresGhost.opened.identity x.rem.val k .sending
                answers.isTrustedIdentity := by
              rcases ht0 : answers.isTrustedIdentity with _ | (_ | _)
              · simp only [ht0] at hid; rw [← ht0]; exact hid.1
              · simp only [ht0] at hid; rw [← ht0]; exact hid.1
              · simp only [ht0] at hid
                rcases hs0 : answers.saveIdentity with _ | _
                · simp only [hs0] at hid; rw [← ht0]; exact hid.1
                · simp only [hs0] at hid
                  rcases hst0 : answers.storeSession with _ | ⟨⟩ <;>
                    (simp only [hst0] at hid; rw [← ht0]; exact hid.1)
            obtain ⟨t, ht_mod, ht_ans⟩ := htrRel
            have hcli_tr' : cliAns.isTrustedIdentity = .ok t := hcli_tr.trans ht_mod
            cases t with
            | false =>
              simp only [ht_ans, hcli_tr']
              exact ⟨trivial, by simp, rfl, fun _ h => nomatch h⟩
            | true =>
              simp only [ht_ans, hcli_tr'] at hcalls hid ⊢
              have hsvRel : ikit.saveRel StoresGhost.opened.identity x.rem.val k
                  answers.saveIdentity := by
                rcases hs0 : answers.saveIdentity with _ | _
                · simp only [hs0] at hid; rw [← hs0]; exact hid.2.1
                · simp only [hs0] at hid
                  rcases hst0 : answers.storeSession with _ | ⟨⟩ <;>
                    (simp only [hst0] at hid; rw [← hs0]; exact hid.2.1)
              obtain ⟨chg, hchg_mod, hchg_ans⟩ := hsvRel
              have hcli_sv' : cliAns.saveIdentity = .ok chg := hcli_sv.trans hchg_mod
              simp only [hchg_ans, hcli_sv'] at hcalls hid ⊢
              have hstRel : answers.storeSession = .ok () := by
                rcases hst : answers.storeSession with ⟨⟩ | ⟨⟩
                · simp only [hst] at hcalls; rw [← hst]; exact hcalls.2.1
                · rfl
              have hcli_st : cliAns.storeSession = .ok () := rfl
              simp only [hstRel, hcli_st]
              refine ⟨trivial, by simp, rfl, ?_⟩
              intro _ _ pw hpw
              rw [writes_save_store] at hpw
              simp only [List.mem_append, List.mem_singleton] at hpw
              rcases hpw with hpw_id | rfl
              · unfold IdGhost.saveUpd at hpw_id
                split at hpw_id
                · simp only [StoresGhost.opened, DirGhost.new, DirGhost.put, DirGhost.setOrPush,
                    DirGhost.writes, List.map, List.mem_singleton] at hpw_id
                  subst hpw_id
                  exact ⟨hok.idPathOk, hok.idPathLt⟩
                · simp [StoresGhost.opened, DirGhost.new, DirGhost.writes] at hpw_id
              · exact ⟨hok.sessPathOk, hok.sessPathLt⟩

end CryptoVerification.SignalSession.Cli.RunProofs.EncryptLemmas
