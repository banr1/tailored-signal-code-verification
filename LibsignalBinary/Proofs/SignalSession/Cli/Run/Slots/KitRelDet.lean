/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.LoadRec
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ScopeIn
public import LibsignalBinary.Proofs.SessionRecordMin.Deserialize
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Segs
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOk
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOk
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Glue.FsTraced
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Epochs
import LibsignalBinary.Proofs.E2E.HooksE.TripleRatchetHooksCommon
import LibsignalBinary.Proofs.E2E.V1.ReachSteps
import LibsignalBinary.Proofs.SessionRecordAt.Swarm.TRREF.B3DeserQ.B3DeserQ
import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkCli
import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCli
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFs
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Glue.BcmpHook
import LibsignalBinary.Proofs.SignalSession.Cli.Run.ReadFileHook
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSat
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.Oblig.EncSessionInj
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.TrapBridge
import LibsignalBinary.Proofs.SignalSession.Cli.Store.SerGlueX
import LibsignalBinary.Proofs.TripleRatchet.Glue
import LibsignalBinary.Proofs.TripleRatchet.Hooks
import LibsignalBinary.Proofs.SignalSession.Cli.Store.SerGlueXCli -- shake: keep

/-!
# CLI Store Kit Answer Determinism, Record Scope Preservation, and Trap-Program Kit Glue

Proves functional answer relations for the CLI session and identity store kits (`cliSessLoadRel_eq`,
`cliSessStoreRel_eq`, `cliIdTrustRel_eq`, `cliIdSaveRel_eq`), `scopeKit` projections, record scope
and `< 2^32` encoded-length preservation across SPQR V1 decrypt/encrypt steps (`decryptRecord_recOk_of_scopeIn`,
`storedRecord_recOk_of_scopeIn`, `cliDecModelRecOkAt_opened`, `cliEncRecOk_opened`), and session and
identity kit contract bundles on `cliExterns W`, `trTrapExterns W.C (cliExterns W)`, and
`cliExternsWith ext`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.Slots

open Arm64 ProofLib ProofLib.Variant SepProp
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.KitInst
open CryptoVerification.SignalSession.Cli.KitInst.SessKit
open CryptoVerification.SignalSession.Cli.KitInst.IdKit
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton

/-! ## 1. Functional answer relations of the CLI store kits -/

/-- `loadRel` is functional for any `DirGhost` whenever `encodeRecord` is injective on `Scope`. -/
theorem cliSessLoadRel_eq {A : RustAlloc} {b : BitVec 64} {rd : ReadRule} {F : FsFiles}
    {pathOk : List (BitVec 8) → Prop} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {peer : AddrGhost} {s1 s2 s3 s4 : Nat} {d : DirGhost} {rem : AddrVal}
    {ans₁ ans₂ : Except Unit (Option (SessionRecord (List (BitVec 8))))}
    (hinj : ∀ ⦃r₁ r₂⦄, Scope r₁ → Scope r₂ →
      E2E.Record.encodeRecord r₁ = E2E.Record.encodeRecord r₂ → r₁ = r₂)
    (h₁ : (cliSessionStoreSpec A b rd F pathOk Scope peer s1 s2 s3 s4).loadRel d rem ans₁)
    (h₂ : (cliSessionStoreSpec A b rd F pathOk Scope peer s1 s2 s3 s4).loadRel d rem ans₂) :
    ans₁ = ans₂ := by
  obtain ⟨bs₁, hg₁, ha₁⟩ := h₁
  obtain ⟨bs₂, hg₂, ha₂⟩ := h₂
  rw [hg₁] at hg₂
  injection hg₂ with hbs
  subst hbs
  cases bs₁ with
  | nil =>
    exact ha₁.trans ha₂.symm
  | cons x xs =>
    obtain ⟨r₁, hr₁, he₁, hs₁⟩ := ha₁
    obtain ⟨r₂, hr₂, he₂, hs₂⟩ := ha₂
    have hreq : r₁ = r₂ := hinj hs₁ hs₂ (he₁.trans he₂.symm)
    subst hreq
    exact hr₁.trans hr₂.symm

/-- Specialization of `cliSessLoadRel_eq` at `StoresGhost.opened.sessions`. -/
theorem cliSessLoadRel_opened_eq {A : RustAlloc} {b : BitVec 64}
    {pathOk : List (BitVec 8) → Prop} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {peer : AddrGhost} {s1 s2 s3 s4 : Nat}
    {ans₁ ans₂ : Except Unit (Option (SessionRecord (List (BitVec 8))))}
    (hinj : ∀ ⦃r₁ r₂⦄, Scope r₁ → Scope r₂ →
      E2E.Record.encodeRecord r₁ = E2E.Record.encodeRecord r₂ → r₁ = r₂)
    (_hok : FilesOkPeer Scope F peer.val)
    (h₁ : (cliSessionStoreSpec A b cliIo.rd F pathOk Scope peer s1 s2 s3 s4).loadRel
      StoresGhost.opened.sessions peer.val ans₁)
    (h₂ : (cliSessionStoreSpec A b cliIo.rd F pathOk Scope peer s1 s2 s3 s4).loadRel
      StoresGhost.opened.sessions peer.val ans₂) :
    ans₁ = ans₂ :=
  cliSessLoadRel_eq hinj h₁ h₂

theorem cliSessLoadRel_eq_loadRec {A : RustAlloc} {b : BitVec 64}
    {pathOk : List (BitVec 8) → Prop} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {peer : AddrGhost} {rem : AddrVal} {s1 s2 s3 s4 : Nat}
    {ans : Except Unit (Option (SessionRecord (List (BitVec 8))))}
    (hinj : EncodeInjOn Scope)
    (h : (cliSessionStoreSpec A b cliIo.rd F pathOk Scope peer s1 s2 s3 s4).loadRel
      StoresGhost.opened.sessions rem ans) :
    ans = loadRec Scope F rem := by
  obtain ⟨bs, hget, hans⟩ := h
  exact loadRec_unique hinj (hget ▸ hans)

/-- On a well-formed peer file (`FilesOkPeer Scope₁ F peer`), enlarging `Scope₁` to `Scope₂` with `EncodeInjOn Scope₂` leaves `loadRec` unchanged. -/
theorem loadRec_of_sub {Scope₁ Scope₂ : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {peer : AddrVal}
    (hinj₂ : EncodeInjOn Scope₂)
    (hsub : ∀ r, Scope₁ r → Scope₂ r)
    (hok : FilesOkPeer Scope₁ F peer) :
    loadRec Scope₁ F peer = loadRec Scope₂ F peer := by
  have hans₁ : SessLoadAns Scope₁ (StoresGhost.opened.sessions.get cliIo.rd F (addressText peer))
      (loadRec Scope₁ F peer) := sessLoadAns_loadRec hok
  have hans₂ : SessLoadAns Scope₂ (StoresGhost.opened.sessions.get cliIo.rd F (addressText peer))
      (loadRec Scope₁ F peer) := by
    rcases hget : StoresGhost.opened.sessions.get cliIo.rd F (addressText peer) with _ | bs
    · rw [hget] at hans₁; exact hans₁
    · cases bs with
      | nil => rw [hget] at hans₁; exact hans₁
      | cons b bs' =>
        rw [hget] at hans₁
        obtain ⟨r, hr, henc, hsc⟩ := hans₁
        exact ⟨r, hr, henc, hsub r hsc⟩
  exact loadRec_unique hinj₂ hans₂

theorem cliSessStoreRel_eq {A : RustAlloc} {b : BitVec 64} {rd : ReadRule} {F : FsFiles}
    {pathOk : List (BitVec 8) → Prop} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {peer : AddrGhost} {s1 s2 s3 s4 : Nat} {d : DirGhost} {rem : AddrVal}
    {r : SessionRecord (List (BitVec 8))} {ans₁ ans₂ : Except Unit Unit}
    (h₁ : (cliSessionStoreSpec A b rd F pathOk Scope peer s1 s2 s3 s4).storeRel d rem r ans₁)
    (h₂ : (cliSessionStoreSpec A b rd F pathOk Scope peer s1 s2 s3 s4).storeRel d rem r ans₂) :
    ans₁ = ans₂ :=
  h₁.trans h₂.symm

theorem cliIdTrustRel_eq {A : RustAlloc} {b : BitVec 64} {rd : ReadRule} {F : FsFiles}
    {pathOk : List (BitVec 8) → Prop} {peer : AddrGhost} {s1 s2 s3 s4 : Nat}
    {g : IdGhost} {rem : AddrVal} {k : IdentityKey} {dir : Direction}
    {ans₁ ans₂ : Except Unit Bool}
    (h₁ : (cliIdentityStoreSpec A b rd F pathOk peer s1 s2 s3 s4).trustRel g rem k dir ans₁)
    (h₂ : (cliIdentityStoreSpec A b rd F pathOk peer s1 s2 s3 s4).trustRel g rem k dir ans₂) :
    ans₁ = ans₂ := by
  obtain ⟨t₁, ht₁, ha₁⟩ := h₁
  obtain ⟨t₂, ht₂, ha₂⟩ := h₂
  rw [ht₁] at ht₂
  injection ht₂ with ht
  subst ht
  exact ha₁.trans ha₂.symm

theorem cliIdSaveRel_eq {A : RustAlloc} {b : BitVec 64} {rd : ReadRule} {F : FsFiles}
    {pathOk : List (BitVec 8) → Prop} {peer : AddrGhost} {s1 s2 s3 s4 : Nat}
    {g : IdGhost} {rem : AddrVal} {k : IdentityKey}
    {ans₁ ans₂ : Except Unit IdentityChange}
    (h₁ : (cliIdentityStoreSpec A b rd F pathOk peer s1 s2 s3 s4).saveRel g rem k ans₁)
    (h₂ : (cliIdentityStoreSpec A b rd F pathOk peer s1 s2 s3 s4).saveRel g rem k ans₂) :
    ans₁ = ans₂ := by
  obtain ⟨c₁, hc₁, ha₁⟩ := h₁
  obtain ⟨c₂, hc₂, ha₂⟩ := h₂
  rw [hc₁] at hc₂
  injection hc₂ with hc
  subst hc
  exact ha₁.trans ha₂.symm

/-! ## 2. Scope projections from `Slots.scopeKit` -/

theorem scopeKit_recordInScopeP {r : SessionRecord (List (BitVec 8))} (h : scopeKit r) :
    CryptoVerification.E2E.RecordX.RecordInScopeP r :=
  h.1.1

theorem scopeKit_recordInScopeEnc {r : SessionRecord (List (BitVec 8))} (h : scopeKit r) :
    MessageEncrypt.RecordInScopeEnc r := by
  intro s hs
  obtain ⟨hseeds, hrc, hky⟩ := h.1.1 s hs
  exact ⟨trivial, hseeds, hrc, hky⟩

theorem scopeKit_pqrState_lt {r : SessionRecord (List (BitVec 8))} (h : scopeKit r)
    (s : Session (List (BitVec 8))) (hs : r.currentSession = some s) :
    s.state.pqRatchetState.length < 2 ^ 32 :=
  h.1.2.1 s hs

/-! ## 3. Opened-store scope pinning and record bounds -/

/-- At `StoresGhost.opened.sessions`, any record in `ScopeAt scopeKit` on a well-formed peer file
(`FilesOkPeer Scope₀ F0 peer.val`, `Scope₀ ⊆ scopeIn`) lies in `Scope₀` and hence in `scopeIn`. -/
theorem cliSess_scopeIn_of_opened {A : RustAlloc} {b : BitVec 64}
    {pathOk : List (BitVec 8) → Prop} {Scope₀ : SessionRecord (List (BitVec 8)) → Prop}
    {F0 : FsFiles} {peer : AddrGhost} {s1 s2 s3 s4 : Nat} {rem : AddrVal}
    {r : SessionRecord (List (BitVec 8))}
    (hsub : ∀ r', Scope₀ r' → scopeIn r')
    (hok : FilesOkPeer Scope₀ F0 peer.val)
    (haddr : (cliSessionStoreSpec A b cliIo.rd F0 pathOk scopeKit peer s1 s2 s3 s4).addrOk rem)
    (hsc : (cliSessionStoreSpec A b cliIo.rd F0 pathOk scopeKit peer s1 s2 s3 s4).ScopeAt
      scopeKit StoresGhost.opened.sessions rem r) :
    Scope₀ r ∧ scopeIn r := by
  have hrem : rem = peer.val := haddr
  subst hrem
  obtain ⟨hkit, bs, hget, hans⟩ := hsc
  obtain ⟨bs₀, hget₀, hwf⟩ := hok.sessGet
  rw [hget] at hget₀
  injection hget₀ with hbs
  subst hbs
  cases bs with
  | nil => cases hans
  | cons b₀ bs' =>
    obtain ⟨r', hr', henc, _⟩ := hans
    injection hr' with hr'
    injection hr' with hr'
    subst hr'
    rcases hwf with hnil | ⟨r₀, henc₀, hsc₀⟩
    · cases hnil
    · have hkit₀ : scopeKit r₀ := scopeKit_of_scopeIn (hsub r₀ hsc₀)
      have heq : r = r₀ :=
        encodeInjOn_deserializeScopeP_Q r r₀ hkit hkit₀ (henc.trans henc₀.symm)
      subst heq
      exact ⟨hsc₀, hsub r hsc₀⟩

private theorem stripPq_bounded_of_parts {s : Session (List (BitVec 8))}
    (hseeds : SeedsLen32 s.state)
    (hrc : s.state.receiverChains.length ≤ maxReceiverChains)
    (hrep : CryptoVerification.E2E.Reach.SessRepr s.state)
    (hwf : s.Wf)
    (hp : ∀ p, s.pendingPreKey = some p → p.timestamp = 0)
    (hk : ∀ k, s.pendingKyberPreKey = some k → k.ciphertext.length = 1569)
    (ha : s.aliceBaseKey = [] ∨ s.aliceBaseKey.length = 33) :
    CryptoVerification.E2E.RecordX.DeserializeScopeBounded ⟨some (PqValid.stripPq s)⟩ := by
  have hscP : CryptoVerification.E2E.RecordX.SessionScopeP (PqValid.stripPq s) := by
    refine ⟨hrc, hp, hk, ha⟩
  refine ⟨⟨?_, ?_, ?_⟩, PqValid.stripPq s, rfl,
    CryptoVerification.E2E.RecordX.sessionScopeBounded_of_sessionScopeP hscP⟩
  · intro t ht
    injection ht with ht; subst ht
    refine ⟨hseeds, Nat.lt_of_le_of_lt hrc (by decide), fun k hk' => ?_⟩
    rw [hk k hk']; decide
  · intro t ht
    injection ht with ht; subst ht
    rfl
  · intro t ht
    injection ht with ht; subst ht
    refine ⟨hrep.1, hrep.2, hwf, ?_⟩
    dsimp only [PqValid.stripPq]
    rcases ha with ha | ha <;> rw [ha] <;> decide

/-- A successful `decryptRecord` step at `spqrV1 C.F K` maps any `scopeIn` record to a `scopeKit`
record whose canonical encoding has length `< 2^32`. -/
theorem decryptRecord_recOk_of_scopeIn {C : Crypto} {K : CryptoVerification.LibsignalSpqrV1.MlKem}
    {parse : UuidParser} {x : DecryptGhost}
    {rec rec' : SessionRecord (List (BitVec 8))} {pt : List (BitVec 8)}
    (hIn : scopeIn rec)
    (hDec : MessageDecrypt.decryptRecord C (CryptoVerification.LibsignalSpqrV1.spqrV1 C.F K)
      parse x rec = .ok (pt, rec')) :
    scopeKit rec' ∧ (E2E.Record.encodeRecord rec').length < 2 ^ 32 := by
  obtain ⟨⟨hInP, hPqIn, hRep⟩, ses, hCur, hSessSc⟩ := hIn
  unfold MessageDecrypt.decryptRecord SessionRecord.tryDecryptFromRecord at hDec
  rw [hCur] at hDec
  dsimp only at hDec
  rcases hTry : SessionState.tryDecryptFromRecord C
      (CryptoVerification.LibsignalSpqrV1.spqrV1 C.F K).spqr
      (serializeAddrVals (serviceIdParse parse) x.rem.val x.loc.val)
      x.msg .whisper (coinsOf x.rest) ses.state with ⟨e | ptext, st'⟩
  · rw [hTry] at hDec; cases hDec
  · rw [hTry] at hDec
    simp only [Except.ok.injEq, Prod.mk.injEq] at hDec
    rcases hDec with ⟨rfl, rfl⟩
    obtain ⟨hSeeds, _, _⟩ := hInP ses hCur
    have hPqSes : PqValid.PqInV1 ses.state.pqRatchetState := hPqIn ses hCur
    obtain ⟨hRep1, hRep2, _, _⟩ := hRep ses hCur
    obtain ⟨hRC, _, _, hAbk⟩ := hSessSc
    obtain ⟨hSeeds', hRC', _, _, key, hRecv⟩ :=
      CryptoVerification.E2E.V1.tryDecryptFromRecord_ok_props_gen C
        (CryptoVerification.LibsignalSpqrV1.spqrV1 C.F K).spqr
        (serializeAddrVals (serviceIdParse parse) x.rem.val x.loc.val)
        x.msg .whisper (coinsOf x.rest) ses.state st' ptext hSeeds hRC hTry
    have hRep' : CryptoVerification.E2E.Reach.SessRepr st' :=
      CryptoVerification.E2E.V1.sessRepr_tryDecryptFromRecord_gen C
        (CryptoVerification.LibsignalSpqrV1.spqrV1 C.F K).spqr
        (serializeAddrVals (serviceIdParse parse) x.rem.val x.loc.val)
        x.msg .whisper (coinsOf x.rest) ses.state st' ptext ⟨hRep1, hRep2⟩ hTry
    have hPqOut : PqValid.PqOutV1 st'.pqRatchetState :=
      (PqValid.pqStep_spqrV1 C.F K).recv ses.state.pqRatchetState x.msg.pqRatchet
        st'.pqRatchetState key hPqSes hRecv
    have hPqLt : st'.pqRatchetState.length < 2 ^ 32 :=
      (PqValid.pqStep_spqrV1 C.F K).out_bound st'.pqRatchetState hPqOut
    have hPendFalse : st'.pendingPreKey = false := by
      unfold SessionState.tryDecryptFromRecord at hTry
      split_ifs at hTry
      · simp at hTry
      · rcases hd : Mut.exec (SessionState.tryDecryptWithState C
            (CryptoVerification.LibsignalSpqrV1.spqrV1 C.F K).spqr
            (serializeAddrVals (serviceIdParse parse) x.rem.val x.loc.val)
            x.msg .whisper (coinsOf x.rest)) ses.state with ⟨e | ptext', updated⟩
        · simp [hd] at hTry
        · rw [hd] at hTry
          simp only [Prod.mk.injEq] at hTry
          rcases hTry with ⟨_, rfl⟩
          unfold SessionState.tryDecryptWithState TripleRatchet.fromSessionState
            SessionState.takeRatchetState SessionState.takePqRatchetState at hd
          rcases hrem : ses.state.remoteIdentity with _ | remote
          · simp [hrem, CryptoVerification.E2E.Epochs.exec_bind,
              CryptoVerification.E2E.Epochs.exec_modifyGet,
              CryptoVerification.E2E.Epochs.exec_get,
              CryptoVerification.E2E.Epochs.exec_throw] at hd
          · simp only [hrem, CryptoVerification.E2E.Epochs.exec_bind,
              CryptoVerification.E2E.Epochs.exec_modifyGet,
              CryptoVerification.E2E.Epochs.exec_get,
              CryptoVerification.E2E.Epochs.exec_pure] at hd
            rcases hdec : Mut.exec (TripleRatchet.decrypt C
                (CryptoVerification.LibsignalSpqrV1.spqrV1 C.F K).spqr
                (serializeAddrVals (serviceIdParse parse) x.rem.val x.loc.val)
                x.msg .whisper (coinsOf x.rest))
                ⟨⟨ses.state.rootKey, ses.state.senderChain, ses.state.receiverChains,
                  ses.state.previousCounter, maxForwardJumps⟩,
                  ses.state.pqRatchetState, ses.state.localIdentity, remote⟩ with ⟨e | pt', tr'⟩
            · rw [hdec] at hd
              simp [CryptoVerification.E2E.Epochs.exec_liftE] at hd
            · rw [hdec] at hd
              simp only [CryptoVerification.E2E.Epochs.exec_liftE,
                CryptoVerification.E2E.Epochs.exec_modify,
                Prod.mk.injEq, Except.ok.injEq] at hd
              rcases hd with ⟨_, rfl⟩
              rfl
    let ses' : Session (List (BitVec 8)) :=
      { ses with state := st', pendingPreKey := none, pendingKyberPreKey := none }
    have hWf' : ses'.Wf := by
      unfold Session.Wf
      dsimp only [ses']
      exact hPendFalse
    have hPendTs' : ∀ p, ses'.pendingPreKey = some p → p.timestamp = 0 := by
      intro _ hp; cases hp
    have hKyber' : ∀ k, ses'.pendingKyberPreKey = some k → k.ciphertext.length = 1569 := by
      intro _ hk; cases hk
    have hScP' : CryptoVerification.E2E.RecordX.SessionScopeP ses' :=
      ⟨hRC', hPendTs', hKyber', hAbk⟩
    have hKit' : scopeKit ⟨some ses'⟩ := by
      refine ⟨⟨?_, ?_, ?_⟩, ses', rfl, hScP'⟩
      · intro s hs; injection hs with hs; subst hs
        exact ⟨hSeeds', Nat.lt_of_le_of_lt hRC' (by decide), fun _ hk => by cases hk⟩
      · intro s hs; injection hs with hs; subst hs
        exact hPqLt
      · intro s hs; injection hs with hs; subst hs
        refine ⟨hRep'.1, hRep'.2, hWf', ?_⟩
        dsimp only [ses']
        rcases hAbk with ha | ha <;> rw [ha] <;> decide
    have hBdd' : CryptoVerification.E2E.RecordX.DeserializeScopeBounded
        ⟨some (PqValid.stripPq ses')⟩ :=
      stripPq_bounded_of_parts hSeeds' hRC' hRep' hWf' hPendTs' hKyber' hAbk
    exact ⟨hKit', PqValid.encodeRecord_length_lt_32_of_stripPq_bounded hBdd' hPqOut⟩

private theorem messageEncrypt_of_from_encrypt {C : Crypto} {codec : SignalMessageProtoCodec}
    {S : Spqr (List (BitVec 8)) (List (BitVec 8))}
    {addrs : Option (List (BitVec 8))} {ptext coins : List (BitVec 8)}
    {st taken : SessionState (List (BitVec 8))}
    {otr otr' : OutgoingTripleRatchet (List (BitVec 8))} {sm : SignalMessage}
    (hfrom : execOk OutgoingTripleRatchet.fromSessionState st = .ok (otr, taken))
    (henc : execOk (OutgoingTripleRatchet.encrypt C codec S ptext
        (st.encryptAddresses addrs) coins) otr = .ok (sm, otr')) :
    SessionState.messageEncrypt C codec S addrs ptext coins st =
      (.ok sm, otr'.applyToSessionState taken) := by
  unfold SessionState.messageEncrypt
  unfold execOk at hfrom henc
  rcases hf : Mut.exec OutgoingTripleRatchet.fromSessionState st with ⟨e | otr₀, taken₀⟩
  · rw [hf] at hfrom; cases hfrom
  · rw [hf] at hfrom
    injection hfrom with hfrom
    injection hfrom with hotr htak
    subst hotr htak
    dsimp only
    rcases he : Mut.exec (OutgoingTripleRatchet.encrypt C codec S ptext
        (st.encryptAddresses addrs) coins) otr₀ with ⟨e | sm₀, otr₁⟩
    · rw [he] at henc; cases henc
    · rw [he] at henc
      injection henc with henc
      injection henc with hsm hotr'
      subst hsm hotr'
      rfl

set_option linter.unusedSimpArgs false in
private theorem fromSessionState_pendingPreKey {s taken : SessionState (List (BitVec 8))}
    {otr : OutgoingTripleRatchet (List (BitVec 8))}
    (h : execOk OutgoingTripleRatchet.fromSessionState s = .ok (otr, taken)) :
    taken.pendingPreKey = s.pendingPreKey := by
  unfold execOk Mut.exec OutgoingTripleRatchet.fromSessionState
    SessionState.takePqRatchetState at h
  rcases hs : s.senderChain with _ | sc <;> rcases hr : s.remoteIdentity with _ | rk <;>
    simp only [hs, hr, modifyGet, MonadStateOf.modifyGet, ExceptT.run, StateT.run, bind,
      ExceptT.bind, ExceptT.mk, ExceptT.lift, ExceptT.bindCont, StateT.bind, Pure.pure,
      ExceptT.pure, StateT.pure, StateT.modifyGet, throw, throwThe, MonadExceptOf.throw, liftM,
      monadLift, MonadLift.monadLift, MonadLiftT.monadLift, StateT.map, Functor.map, get, getThe,
      MonadStateOf.get, StateT.get, reduceCtorEq] at h
  all_goals (try split_ifs at h) <;>
    simp only [ExceptT.bindCont, StateT.bind, StateT.pure, Pure.pure, bind, reduceCtorEq,
      Except.ok.injEq, Prod.mk.injEq] at h
  exact h.2 ▸ rfl

/-- A successful `StepsThroughEncrypt` step at `spqrV1 C.F K` from a `scopeIn` record produces a
`storedRecord` in `scopeKit` whose canonical encoding has length `< 2^32`. -/
theorem storedRecord_recOk_of_scopeIn {C : Crypto} {K : CryptoVerification.LibsignalSpqrV1.MlKem}
    {parse : UuidParser} {x : MessageEncrypt.WithStoresEncGhost}
    {r : SessionRecord (List (BitVec 8))} {sess : Session (List (BitVec 8))}
    {otr otr' : OutgoingTripleRatchet (List (BitVec 8))}
    {taken : SessionState (List (BitVec 8))} {k : IdentityKey} {m : CiphertextMessage}
    (hStep : MessageEncrypt.StepsThroughEncrypt scopeIn C
      (CryptoVerification.LibsignalSpqrV1.spqrV1 C.F K) parse x r sess otr taken k m otr') :
    scopeKit (MessageEncrypt.storedRecord sess otr' taken) ∧
      (E2E.Record.encodeRecord (MessageEncrypt.storedRecord sess otr' taken)).length < 2 ^ 32 := by
  obtain ⟨hCur, hIn, hFrom, _, hEncStep⟩ := hStep
  obtain ⟨⟨hInP, hPqIn, hRep⟩, ses₀, hCur₀, hSessSc⟩ := hIn
  rw [hCur] at hCur₀; injection hCur₀ with hses; subst hses
  obtain ⟨hSeeds, _, _⟩ := hInP sess hCur
  have hPqSes : PqValid.PqInV1 sess.state.pqRatchetState := hPqIn sess hCur
  obtain ⟨hRep1, hRep2, hWf, hAbk32⟩ := hRep sess hCur
  obtain ⟨hRC, hPendTs, hKyber, hAbk⟩ := hSessSc
  let addrs := serializeAddrVals (serviceIdParse parse) x.loc.val x.rem.val
  have hExEnc : ∃ sm,
      execOk (OutgoingTripleRatchet.encrypt C protoSignalCodec
        (CryptoVerification.LibsignalSpqrV1.spqrV1 C.F K).spqr x.ptext
        (sess.state.encryptAddresses addrs) x.rest) otr = .ok (sm, otr') := by
    unfold MessageEncrypt.EncEncryptStep at hEncStep
    cases hp : sess.pendingPreKey with
    | none =>
      rw [hp] at hEncStep
      obtain ⟨sm, henc, _⟩ := hEncStep
      have hpf : sess.state.pendingPreKey = false := by
        unfold Session.Wf at hWf; rw [hWf, hp]; rfl
      have hea : sess.state.encryptAddresses addrs = none := by
        simp [SessionState.encryptAddresses, hpf]
      rw [hea]
      exact ⟨sm, henc⟩
    | some items =>
      rw [hp] at hEncStep
      obtain ⟨_, _, sm, _, _, _, henc, _⟩ := hEncStep
      have hpt : sess.state.pendingPreKey = true := by
        unfold Session.Wf at hWf; rw [hWf, hp]; rfl
      have hea : sess.state.encryptAddresses addrs = addrs := by
        simp [SessionState.encryptAddresses, hpt]
      rw [hea]
      exact ⟨sm, henc⟩
  obtain ⟨sm, hEnc⟩ := hExEnc
  have hMsgEnc := messageEncrypt_of_from_encrypt hFrom hEnc
  let st' := otr'.applyToSessionState taken
  obtain ⟨hSeeds', hRC', _, _, key, pm, hSend, _⟩ :=
    CryptoVerification.E2E.V1.messageEncrypt_ok_props_gen C protoSignalCodec
      (CryptoVerification.LibsignalSpqrV1.spqrV1 C.F K).spqr addrs x.ptext x.rest
      sess.state st' sm hSeeds hRC hMsgEnc
  have hRep' : CryptoVerification.E2E.Reach.SessRepr st' :=
    CryptoVerification.E2E.V1.sessRepr_messageEncrypt_gen C protoSignalCodec
      (CryptoVerification.LibsignalSpqrV1.spqrV1 C.F K).spqr addrs x.ptext x.rest
      sess.state st' sm ⟨hRep1, hRep2⟩ hMsgEnc
  have hPqOut : PqValid.PqOutV1 st'.pqRatchetState :=
    (PqValid.pqStep_spqrV1 C.F K).send sess.state.pqRatchetState x.rest st'.pqRatchetState
      key pm hPqSes hSend
  have hPqLt : st'.pqRatchetState.length < 2 ^ 32 :=
    (PqValid.pqStep_spqrV1 C.F K).out_bound st'.pqRatchetState hPqOut
  have hPendEq : st'.pendingPreKey = sess.state.pendingPreKey := by
    simpa [st', OutgoingTripleRatchet.applyToSessionState] using
      fromSessionState_pendingPreKey hFrom
  let ses' : Session (List (BitVec 8)) := { sess with state := st' }
  have hWf' : ses'.Wf := by
    unfold Session.Wf at hWf ⊢
    dsimp only [ses']
    exact hPendEq.trans hWf
  have hScP' : CryptoVerification.E2E.RecordX.SessionScopeP ses' :=
    ⟨hRC', hPendTs, hKyber, hAbk⟩
  have hKit' : scopeKit (MessageEncrypt.storedRecord sess otr' taken) := by
    refine ⟨⟨?_, ?_, ?_⟩, ses', rfl, hScP'⟩
    · intro s hs; injection hs with hs; subst hs
      refine ⟨hSeeds', Nat.lt_of_le_of_lt hRC' (by decide), fun ky hky => ?_⟩
      rw [hKyber ky hky]; decide
    · intro s hs; injection hs with hs; subst hs
      exact hPqLt
    · intro s hs; injection hs with hs; subst hs
      exact ⟨hRep'.1, hRep'.2, hWf', hAbk32⟩
  have hBdd' : CryptoVerification.E2E.RecordX.DeserializeScopeBounded
      ⟨some (PqValid.stripPq ses')⟩ :=
    stripPq_bounded_of_parts hSeeds' hRC' hRep' hWf' hPendTs hKyber hAbk
  exact ⟨hKit', PqValid.encodeRecord_length_lt_32_of_stripPq_bounded hBdd' hPqOut⟩

/-- `DecModelRecOk` for `cliSessionStoreSpec` whenever `Scope ⊆ scopeIn` and `scopeKit ⊆ KitScope`. -/
theorem cliDecModelRecOk_of_scopeIn {A : RustAlloc} {b : BitVec 64} {rd : ReadRule} {F0 : FsFiles}
    {pathOk : List (BitVec 8) → Prop}
    {KitScope Scope : SessionRecord (List (BitVec 8)) → Prop}
    {peer : AddrGhost} {s1 s2 s3 s4 : Nat}
    {C : Crypto} {K : CryptoVerification.LibsignalSpqrV1.MlKem} {parse : UuidParser}
    (hIn : ∀ r, Scope r → scopeIn r)
    (hOut : ∀ r', scopeKit r' → KitScope r') :
    MessageDecrypt.DecModelRecOk
      (cliSessionStoreSpec A b rd F0 pathOk KitScope peer s1 s2 s3 s4)
      C (CryptoVerification.LibsignalSpqrV1.spqrV1 C.F K) parse Scope := by
  intro x _st0 rec rec' pt hScopeAt hDec
  obtain ⟨hKit, hLen⟩ := decryptRecord_recOk_of_scopeIn (hIn rec hScopeAt.1) hDec
  exact ⟨hOut rec' hKit, hLen⟩

/-- Fixed-`st0`, `kit.addrOk`-guarded variant of `DecModelRecOk`. -/
def DecModelRecOkAt {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (st0 : kit.StoreState)
    (C : Crypto) (S : SpqrModel) (parse : UuidParser)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  ∀ (x : DecryptGhost) (rec rec' : SessionRecord (List (BitVec 8)))
    (pt : List (BitVec 8)),
    kit.addrOk x.rem.val →
    kit.ScopeAt Scope st0 x.rem.val rec →
    MessageDecrypt.decryptRecord C S parse x rec = .ok (pt, rec') →
    kit.RecOk rec'

/-- `DecModelRecOkAt` at `StoresGhost.opened.sessions` and `scopeKit` on a well-formed peer file (`Scope₀ ⊆ scopeIn`). -/
theorem cliDecModelRecOkAt_opened {A : RustAlloc} {b : BitVec 64}
    {pathOk : List (BitVec 8) → Prop} {Scope₀ : SessionRecord (List (BitVec 8)) → Prop}
    {F0 : FsFiles} {peer : AddrGhost} {s1 s2 s3 s4 : Nat}
    {C : Crypto} {K : CryptoVerification.LibsignalSpqrV1.MlKem} {parse : UuidParser}
    (hsub : ∀ r', Scope₀ r' → scopeIn r')
    (hok : FilesOkPeer Scope₀ F0 peer.val) :
    DecModelRecOkAt
      (cliSessionStoreSpec A b cliIo.rd F0 pathOk scopeKit peer s1 s2 s3 s4)
      StoresGhost.opened.sessions
      C (CryptoVerification.LibsignalSpqrV1.spqrV1 C.F K) parse scopeKit := by
  intro x rec rec' pt haddr hsc hdec
  have hIn : scopeIn rec := (cliSess_scopeIn_of_opened hsub hok haddr hsc).2
  exact decryptRecord_recOk_of_scopeIn hIn hdec

/-- `storedRecord` satisfies `kit.RecOk` at `StoresGhost.opened.sessions` and `scopeKit` on a well-formed peer file (`Scope₀ ⊆ scopeIn`). -/
theorem cliEncRecOk_opened {A : RustAlloc} {b : BitVec 64}
    {pathOk : List (BitVec 8) → Prop} {Scope₀ : SessionRecord (List (BitVec 8)) → Prop}
    {F0 : FsFiles} {peer : AddrGhost} {s1 s2 s3 s4 : Nat}
    {C : Crypto} {K : CryptoVerification.LibsignalSpqrV1.MlKem} {parse : UuidParser}
    {x : MessageEncrypt.WithStoresEncGhost} {r : SessionRecord (List (BitVec 8))}
    {sess : Session (List (BitVec 8))} {otr otr' : OutgoingTripleRatchet (List (BitVec 8))}
    {taken : SessionState (List (BitVec 8))} {k : IdentityKey} {m : CiphertextMessage}
    (hsub : ∀ r', Scope₀ r' → scopeIn r')
    (hok : FilesOkPeer Scope₀ F0 peer.val)
    (haddr : (cliSessionStoreSpec A b cliIo.rd F0 pathOk scopeKit peer s1 s2 s3 s4).addrOk x.rem.val)
    (hStep : MessageEncrypt.StepsThroughEncrypt
      ((cliSessionStoreSpec A b cliIo.rd F0 pathOk scopeKit peer s1 s2 s3 s4).ScopeAt
        scopeKit StoresGhost.opened.sessions x.rem.val)
      C (CryptoVerification.LibsignalSpqrV1.spqrV1 C.F K) parse x r sess otr taken k m otr') :
    (cliSessionStoreSpec A b cliIo.rd F0 pathOk scopeKit peer s1 s2 s3 s4).RecOk
      (MessageEncrypt.storedRecord sess otr' taken) := by
  obtain ⟨hCur, hScAt, hFrom, hRemId, hEnc⟩ := hStep
  have hIn : scopeIn r := (cliSess_scopeIn_of_opened hsub hok haddr hScAt).2
  exact storedRecord_recOk_of_scopeIn ⟨hCur, hIn, hFrom, hRemId, hEnc⟩

/-! ## 4. `Stage2ContractsMin`, `SessionRecord::deserialize` at `scopeKit`, and trap-program kit glue -/

theorem trTrapExterns_cli_eq (W : CliHooks) {n : String}
    (hn : n ≠ rngFillName) (hnp : Rust.isPanicSymbol n = false) :
    trTrapExterns W.C (cliExterns W) n = cliExterns W n := by
  have h1 : Rust.withPanics (trTrapExterns W.C (cliExterns W)) n =
      trTrapExterns W.C (cliExterns W) n := by
    simp [Rust.withPanics, hnp]
  rw [← h1, withPanics_trTrap_ne W.C (cliExterns W) hn,
    cliExterns_agree W 0#64 hn, congrFun (withPanics_cliExterns W) n]

theorem hookSat_trTrap_of_cli {α : Type} (W : CliHooks) {n : String} {spec : Spec α}
    (hn : n ≠ rngFillName) (hnp : Rust.isPanicSymbol n = false)
    (h : HookSat (cliExterns W) n spec) :
    HookSat (trTrapExterns W.C (cliExterns W)) n spec := by
  rcases h with ⟨fn, hfn, hok⟩
  exact ⟨fn, (trTrapExterns_cli_eq W hn hnp).trans hfn, hok⟩

theorem trTrap_stub_ok {α : Type} (W : CliHooks) (img : Obj.Image) {name : String}
    {h : State → State} {spec : Spec α} {stub : Nat}
    (hfn : libsignalSessionCode.fnOff name = stub) (hs : stub < 2 ^ 64)
    (hstub : ∀ H, (libsignalSessionCode.rebase 0 H).hookAtOff? stub = H name)
    (hn : name ≠ rngFillName) (hnp : Rust.isPanicSymbol name = false)
    (hrow : (name, h) ∈ cliHookTable W) (hh : HookOk h spec) :
    subroutine_ok (mProg img (trTrapExterns W.C (cliExterns W)))
      ((mProg img (trTrapExterns W.C (cliExterns W))).fnAddr name) spec := by
  have hsat : HookSat (trTrapExterns W.C (cliExterns W)) name spec :=
    hookSat_trTrap_of_cli W hn hnp ⟨h, cliExterns_row W hrow, hh⟩
  have h1 := hook_ok_at (P := libsignalSessionCode) (b := img.base)
    (hooks := trTrapExterns W.C (cliExterns W))
    (hname := name) (k := 0) hfn (Nat.add_zero _) hs hstub hnp hsat
  simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using h1

theorem shim_trTrap_ok {α : Type} (W : CliHooks) (img : Obj.Image) {spec : Spec α}
    (hh : HookOk hookNoop spec) :
    subroutine_ok (mProg img (trTrapExterns W.C (cliExterns W)))
      ((mProg img (trTrapExterns W.C (cliExterns W))).fnAddr shimName) spec :=
  trTrap_stub_ok W img shim_fnOff (by decide)
    (ls_hook% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
    (by decide) (by simp [Rust.isPanicSymbol, shimName]) (shim_row W) hh

theorem alloc_trTrap_ok {α : Type} (W : CliHooks) (img : Obj.Image) {spec : Spec α}
    (hh : HookOk E2E.allocHook0 spec) :
    subroutine_ok (mProg img (trTrapExterns W.C (cliExterns W)))
      ((mProg img (trTrapExterns W.C (cliExterns W))).fnAddr allocName) spec :=
  trTrap_stub_ok W img alloc_fnOff (by decide) (ls_hook% "__rustc::__rust_alloc")
    (by decide) (by simp [Rust.isPanicSymbol, allocName]) (alloc_row W) hh

theorem dealloc_trTrap_ok {α : Type} (W : CliHooks) (img : Obj.Image) {spec : Spec α}
    (hh : HookOk E2E.deallocHook spec) :
    subroutine_ok (mProg img (trTrapExterns W.C (cliExterns W)))
      ((mProg img (trTrapExterns W.C (cliExterns W))).fnAddr deallocName) spec :=
  trTrap_stub_ok W img dealloc_fnOff (by decide) (ls_hook% "__rustc::__rust_dealloc")
    (by decide) (by simp [Rust.isPanicSymbol, deallocName]) (dealloc_row W) hh

theorem realloc_trTrap_ok {α : Type} (W : CliHooks) (img : Obj.Image) {spec : Spec α}
    (hh : HookOk E2E.reallocHook0 spec) :
    subroutine_ok (mProg img (trTrapExterns W.C (cliExterns W)))
      ((mProg img (trTrapExterns W.C (cliExterns W))).fnAddr reallocName) spec :=
  trTrap_stub_ok W img realloc_fnOff (by decide) (ls_hook% "__rustc::__rust_realloc")
    (by decide) (by simp [Rust.isPanicSymbol, reallocName]) (realloc_row W) hh

theorem memset_trTrap_ok {α : Type} (W : CliHooks) (img : Obj.Image) {spec : Spec α}
    (hh : HookOk hookMemset spec) :
    subroutine_ok (mProg img (trTrapExterns W.C (cliExterns W)))
      ((mProg img (trTrapExterns W.C (cliExterns W))).fnAddr memsetName) spec :=
  trTrap_stub_ok W img memset_fnOff (by decide) (ls_hook% "memset")
    (by decide) (by simp [Rust.isPanicSymbol, memsetName]) (memset_row W) hh

theorem memmove_trTrap_ok {α : Type} (W : CliHooks) (img : Obj.Image) {spec : Spec α}
    (hh : HookOk hookMemmove spec) :
    subroutine_ok (mProg img (trTrapExterns W.C (cliExterns W)))
      ((mProg img (trTrapExterns W.C (cliExterns W))).fnAddr memmoveName) spec :=
  trTrap_stub_ok W img memmove_fnOff (by decide) (ls_hook% "memmove")
    (by decide) (by simp [Rust.isPanicSymbol, memmoveName]) (memmove_row W) hh

theorem memcpy_trTrap_ok {α : Type} (W : CliHooks) (img : Obj.Image) {spec : Spec α}
    (hh : HookOk hookMemcpy spec) :
    subroutine_ok (mProg img (trTrapExterns W.C (cliExterns W)))
      ((mProg img (trTrapExterns W.C (cliExterns W))).fnAddr memcpyName) spec :=
  trTrap_stub_ok W img memcpy_fnOff (by decide) (ls_hook% "memcpy")
    (by decide) (by simp [Rust.isPanicSymbol, memcpyName]) (memcpy_row W) hh

theorem allocContracts_trTrap (W : CliHooks) (img : Obj.Image) :
    AllocContracts img.base E2E.HooksE.A0 (trTrapExterns W.C (cliExterns W)) where
  alloc := alloc_trTrap_ok W img cliAllocHooks_A0.alloc
  dealloc := dealloc_trTrap_ok W img cliAllocHooks_A0.dealloc
  realloc := realloc_trTrap_ok W img cliAllocHooks_A0.realloc
  shim := shim_trTrap_ok W img sessionShim_hookOk
  memcpy stk := memcpy_trTrap_ok W img (hookMemcpy_ok stk)
  session_memcpy stk := memcpy_trTrap_ok W img (hookMemcpy_trace_ok stk)
  memcpy_region := memcpy_trTrap_ok W img hookMemcpy_region_ok
  session_memcpy_region := memcpy_trTrap_ok W img hookMemcpy_region_trace_ok
  memmove stk := memmove_trTrap_ok W img (hookMemmove_ok stk)
  session_memmove stk := memmove_trTrap_ok W img (hookMemmove_trace_ok stk)
  memset stk hpos := memset_trTrap_ok W img (hookMemset_ok stk hpos)
  session_memset stk hpos := memset_trTrap_ok W img (hookMemset_trace_ok stk hpos)
  memset_region := memset_trTrap_ok W img hookMemset_region_ok
  session_memset_region := memset_trTrap_ok W img hookMemset_region_trace_ok

theorem allocContractsX_trTrap (W : CliHooks) (img : Obj.Image) :
    AllocContractsX img E2E.HooksE.A0 (trTrapExterns W.C (cliExterns W)) where
  alloc := subroutine_ok_inImage_of_subroutine_ok img <| alloc_trTrap_ok W img <|
    hookOk_rustAllocWithStack (stk := extHookStack) cliAllocHooks_A0.alloc
      allocHookStack_le_extHookStack extHookStack_le
  dealloc := subroutine_ok_inImage_of_subroutine_ok img <| dealloc_trTrap_ok W img <|
    hookOk_rustDeallocExternWithStack (stk := extHookStack) cliAllocHooks_A0.dealloc
      allocHookStack_le_extHookStack extHookStack_le
  realloc := subroutine_ok_inImage_of_subroutine_ok img <| realloc_trTrap_ok W img <|
    hookOk_rustReallocExternWithStack (stk := extHookStack) cliAllocHooks_A0.realloc
      allocHookStack_le_extHookStack extHookStack_le
  shim stk _ _ := subroutine_ok_inImage_of_subroutine_ok img <| shim_trTrap_ok W img <|
    hookOk_withStack sessionShim_hookOk stk
  memcpy stk _ _ := subroutine_ok_inImage_of_subroutine_ok img <| memcpy_trTrap_ok W img <|
    hookMemcpy_ok stk
  session_memcpy stk _ _ := subroutine_ok_inImage_of_subroutine_ok img <| memcpy_trTrap_ok W img <|
    hookMemcpy_trace_ok stk
  memcpy_region stk _ _ := subroutine_ok_inImage_of_subroutine_ok img <| memcpy_trTrap_ok W img <|
    hookOk_withStack hookMemcpy_region_ok stk
  session_memcpy_region stk _ _ := subroutine_ok_inImage_of_subroutine_ok img <|
    memcpy_trTrap_ok W img <| hookOk_withStack hookMemcpy_region_trace_ok stk
  memmove stk _ _ := subroutine_ok_inImage_of_subroutine_ok img <| memmove_trTrap_ok W img <|
    hookMemmove_ok stk
  session_memmove stk _ _ := subroutine_ok_inImage_of_subroutine_ok img <| memmove_trTrap_ok W img <|
    hookMemmove_trace_ok stk
  memset stk hle _ := subroutine_ok_inImage_of_subroutine_ok img <| memset_trTrap_ok W img <|
    hookMemset_ok stk (pos_of_extHookStack_le hle)
  session_memset stk hle _ := subroutine_ok_inImage_of_subroutine_ok img <| memset_trTrap_ok W img <|
    hookMemset_trace_ok stk (pos_of_extHookStack_le hle)
  memset_region stk _ _ := subroutine_ok_inImage_of_subroutine_ok img <| memset_trTrap_ok W img <|
    hookOk_withStack hookMemset_region_ok stk
  session_memset_region stk _ _ := subroutine_ok_inImage_of_subroutine_ok img <|
    memset_trTrap_ok W img <| hookOk_withStack hookMemset_region_trace_ok stk

theorem allocContractsFs_trTrap (W : CliHooks) (img : Obj.Image) :
    AllocContractsFs img E2E.HooksE.A0 (trTrapExterns W.C (cliExterns W)) where
  alloc := subroutine_ok_inImage_of_subroutine_ok img <| alloc_trTrap_ok W img <|
    (hookOk_rustAllocWithStack (stk := extHookStack) cliAllocHooks_A0.alloc
      allocHookStack_le_extHookStack extHookStack_le).keepsFs allocHook0_fs
  dealloc := subroutine_ok_inImage_of_subroutine_ok img <| dealloc_trTrap_ok W img <|
    (hookOk_rustDeallocExternWithStack (stk := extHookStack) cliAllocHooks_A0.dealloc
      allocHookStack_le_extHookStack extHookStack_le).keepsFs deallocHook_fs
  realloc := subroutine_ok_inImage_of_subroutine_ok img <| realloc_trTrap_ok W img <|
    (hookOk_rustReallocExternWithStack (stk := extHookStack) cliAllocHooks_A0.realloc
      allocHookStack_le_extHookStack extHookStack_le).keepsFs reallocHook0_fs
  shim stk _ _ := subroutine_ok_inImage_of_subroutine_ok img <| shim_trTrap_ok W img <|
    (hookOk_withStack sessionShim_hookOk stk).keepsFs hookNoop_fs
  memcpy stk _ _ := subroutine_ok_inImage_of_subroutine_ok img <| memcpy_trTrap_ok W img <|
    (hookMemcpy_ok stk).keepsFs hookMemcpy_fs
  session_memcpy stk _ _ := subroutine_ok_inImage_of_subroutine_ok img <| memcpy_trTrap_ok W img <|
    (hookMemcpy_trace_ok stk).keepsFs hookMemcpy_fs
  memcpy_region stk _ _ := subroutine_ok_inImage_of_subroutine_ok img <| memcpy_trTrap_ok W img <|
    (hookOk_withStack hookMemcpy_region_ok stk).keepsFs hookMemcpy_fs
  session_memcpy_region stk _ _ := subroutine_ok_inImage_of_subroutine_ok img <|
    memcpy_trTrap_ok W img <| (hookOk_withStack hookMemcpy_region_trace_ok stk).keepsFs hookMemcpy_fs
  memmove stk _ _ := subroutine_ok_inImage_of_subroutine_ok img <| memmove_trTrap_ok W img <|
    (hookMemmove_ok stk).keepsFs hookMemmove_fs
  session_memmove stk _ _ := subroutine_ok_inImage_of_subroutine_ok img <| memmove_trTrap_ok W img <|
    (hookMemmove_trace_ok stk).keepsFs hookMemmove_fs
  memset stk hle _ := subroutine_ok_inImage_of_subroutine_ok img <| memset_trTrap_ok W img <|
    (hookMemset_ok stk (pos_of_extHookStack_le hle)).keepsFs hookMemset_fs
  session_memset stk hle _ := subroutine_ok_inImage_of_subroutine_ok img <| memset_trTrap_ok W img <|
    (hookMemset_trace_ok stk (pos_of_extHookStack_le hle)).keepsFs hookMemset_fs
  memset_region stk _ _ := subroutine_ok_inImage_of_subroutine_ok img <| memset_trTrap_ok W img <|
    (hookOk_withStack hookMemset_region_ok stk).keepsFs hookMemset_fs
  session_memset_region stk _ _ := subroutine_ok_inImage_of_subroutine_ok img <|
    memset_trTrap_ok W img <| (hookOk_withStack hookMemset_region_trace_ok stk).keepsFs hookMemset_fs
  session_memcpy_region_ro stk _ _ := subroutine_ok_inImage_of_subroutine_ok img <|
    memcpy_trTrap_ok W img <|
      (hookOk_withStack CryptoVerification.SpqrV1.Alloc.hookMemcpy_region_ro_trace_ok stk).keepsFs
        hookMemcpy_fs

private theorem hookOk_withExternStackFromAlloc' {α : Type} {fn : State → State} {spec : Spec α}
    (h : HookOk fn spec)
    (hpan : ∀ x R s0 sf, sf.mem ⊨ spec.onPanic x s0 sf ∗ (memRegion (s0.sp - 16384#64) 12288 ∗ R) →
      sf.mem ⊨ spec.onPanic x s0 sf ∗ R)
    (hexit : ∀ x code R s0 sf,
      ¬ (sf.mem ⊨ spec.onExit x code s0 sf ∗ (memRegion (s0.sp - 16384#64) 12288 ∗ R)))
    (hoom : ∀ x R s0 sf,
      ¬ (sf.mem ⊨ spec.onOom x s0 sf ∗ (memRegion (s0.sp - 16384#64) 12288 ∗ R))) :
    HookOk fn spec.withExternStackFromAlloc' := by
  intro x R s0 hrun hpre hsp
  have hpre' : s0.mem ⊨ spec.pre x s0 ∗ (memRegion (s0.sp - 16384#64) 12288 ∗ R) := by
    simpa only [Spec.withExternStackFromAlloc', sepConj_assoc] using hpre
  obtain ⟨hkf, hsym, hout⟩ := h x (memRegion (s0.sp - 16384#64) 12288 ∗ R) s0 hrun hpre' hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcs, hpost⟩ | ⟨hp_st, hp⟩ | ⟨code, hex_st, he⟩ | ⟨htrap, ho⟩
  · refine Or.inl ⟨hret, hcs, ?_⟩
    simpa only [Spec.withExternStackFromAlloc', sepConj_assoc] using hpost
  · exact Or.inr (Or.inl ⟨hp_st, hpan x R s0 (fn s0) hp⟩)
  · exact False.elim (hexit x code R s0 (fn s0) he)
  · exact False.elim (hoom x R s0 (fn s0) ho)

private theorem deallocLayoutHook0_ok :
    HookOk E2E.deallocHook (Proofs.libsignal.Hooks2.rustDeallocLayoutSpec' E2E.HooksE.A0) := by
  intro ⟨p, size, align⟩ R s0 hrun hpre hsp
  dsimp only [Proofs.libsignal.Hooks2.rustDeallocLayoutSpec'] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact E2E.HooksE.deallocHook_ok (p, size, align) R s0 hrun hpre.2 hsp

private theorem hookOk_withHookStack {α : Type} {fn : State → State} {spec : Spec α}
    (h : HookOk fn spec) (stk : Nat)
    (hpan : ∀ x R s0 sf, ¬ (sf.mem ⊨ spec.onPanic x s0 sf ∗ (stackAt s0.sp stk ∗ R)))
    (hexit : ∀ x code R s0 sf, ¬ (sf.mem ⊨ spec.onExit x code s0 sf ∗ (stackAt s0.sp stk ∗ R)))
    (hoom : ∀ x R s0 sf, ¬ (sf.mem ⊨ spec.onOom x s0 sf ∗ (stackAt s0.sp stk ∗ R))) :
    HookOk fn (spec.withHookStack stk) := by
  intro x R s0 hrun hpre hsp
  have hpre' : s0.mem ⊨ spec.pre x s0 ∗ (stackAt s0.sp stk ∗ R) := by
    simpa only [Spec.withHookStack, sepConj_assoc] using hpre
  obtain ⟨hkf, hsym, hout⟩ := h x (stackAt s0.sp stk ∗ R) s0 hrun hpre' hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcs, hpost⟩ | ⟨_, hp⟩ | ⟨code, _, he⟩ | ⟨_, ho⟩
  · refine Or.inl ⟨hret, hcs, ?_⟩
    simpa only [Spec.withHookStack, sepConj_assoc] using hpost
  · exact False.elim (hpan x R s0 (fn s0) hp)
  · exact False.elim (hexit x code R s0 (fn s0) he)
  · exact False.elim (hoom x R s0 (fn s0) ho)

/-- `Stage2ContractsMin` on `trTrapExterns W.C (cliExterns W)`. -/
theorem stage2ContractsMin_trTrap {img : Obj.Image} (W : CliHooks)
    (himg : Obj.Loads libsignalSessionImage img) :
    Proofs.libsignal.Hooks2.Stage2ContractsMin img (trTrapExterns W.C (cliExterns W)) where
  loads := himg
  alloc_A0 := Proofs.libsignal.Hooks2.sub_ok_at_of_fnAddr
    (Proofs.libsignal.Hooks2.SP2Ext_fnAddr img.base _ allocName) <|
    subroutine_ok_inImage_of_subroutine_ok img <| alloc_trTrap_ok W img <|
    hookOk_withExternStackFromAlloc' E2E.HooksE.allocHook0_ok
      (fun _ _ _ _ hp => False.elim (not_satisfies_false_sepConj hp))
      (fun _ _ _ _ _ he => not_satisfies_false_sepConj he)
      (fun _ _ _ _ ho => not_satisfies_false_sepConj ho)
  deallocLayout_A0 := Proofs.libsignal.Hooks2.sub_ok_at_of_fnAddr
    (Proofs.libsignal.Hooks2.SP2Ext_fnAddr img.base _ deallocName) <|
    subroutine_ok_inImage_of_subroutine_ok img <| dealloc_trTrap_ok W img <|
    hookOk_withExternStackFromAlloc' deallocLayoutHook0_ok
      (fun _ _ _ _ hp => False.elim (not_satisfies_false_sepConj hp))
      (fun _ _ _ _ _ he => not_satisfies_false_sepConj he)
      (fun _ _ _ _ ho => not_satisfies_false_sepConj ho)
  realloc_A0 := Proofs.libsignal.Hooks2.sub_ok_at_of_fnAddr
    (Proofs.libsignal.Hooks2.SP2Ext_fnAddr img.base _ reallocName) <|
    subroutine_ok_inImage_of_subroutine_ok img <| realloc_trTrap_ok W img <|
    hookOk_withExternStackFromAlloc' E2E.HooksE.reallocHook0_ok
      (fun _ _ _ _ hp => False.elim (not_satisfies_false_sepConj hp))
      (fun _ _ _ _ _ he => not_satisfies_false_sepConj he)
      (fun _ _ _ _ ho => not_satisfies_false_sepConj ho)
  shim := Proofs.libsignal.Hooks2.sub_ok_at_of_fnAddr
    (Proofs.libsignal.Hooks2.SP2Ext_fnAddr img.base _ shimName) <|
    subroutine_ok_inImage_of_subroutine_ok img <| shim_trTrap_ok W img <|
    hookOk_withHookStack sessionShim_hookOk CryptoVerification.LibsignalTripleRatchet.extHookStack
      (fun _ _ _ _ hp => not_satisfies_false_sepConj hp)
      (fun _ _ _ _ _ he => not_satisfies_false_sepConj he)
      (fun _ _ _ _ ho => not_satisfies_false_sepConj ho)
  memcpy := Proofs.libsignal.Hooks2.sub_ok_at_of_fnAddr
    (Proofs.libsignal.Hooks2.SP2Ext_fnAddr img.base _ memcpyName) <|
    (allocContractsX_trTrap W img).session_memcpy
      CryptoVerification.LibsignalTripleRatchet.extHookStack (Nat.le_refl _) (by decide)
  memmove := Proofs.libsignal.Hooks2.sub_ok_at_of_fnAddr
    (Proofs.libsignal.Hooks2.SP2Ext_fnAddr img.base _ memmoveName) <|
    (allocContractsX_trTrap W img).session_memmove
      CryptoVerification.LibsignalTripleRatchet.extHookStack (Nat.le_refl _) (by decide)

/-- `Stage2ContractsMin` on `cliExterns W`, transferred from `stage2ContractsMin_trTrap` via `trapsOnly_trTrap_cli`. -/
theorem stage2ContractsMin_cli {img : Obj.Image} (W : CliHooks)
    (himg : Obj.Loads libsignalSessionImage img) :
    Proofs.libsignal.Hooks2.Stage2ContractsMin img (cliExterns W) :=
  let h := stage2ContractsMin_trTrap W himg
  let ht := trapsOnly_trTrap_cli img.base W
  ⟨himg,
   subroutine_ok.of_trapsOnly ht h.alloc_A0,
   subroutine_ok.of_trapsOnly ht h.deallocLayout_A0,
   subroutine_ok.of_trapsOnly ht h.realloc_A0,
   subroutine_ok.of_trapsOnly ht h.shim,
   subroutine_ok.of_trapsOnly ht h.memcpy,
   subroutine_ok.of_trapsOnly ht h.memmove⟩

/-- `SessionRecord::deserialize` satisfies `sessDeserializeSpec scopeKit E2E.HooksE.A0 img` under `Stage2ContractsMin img ext`. -/
theorem sessDeserialize_scopeKit_ok {img : Obj.Image} {ext : String → Option (State → State)}
    (hStage2 : Proofs.libsignal.Hooks2.Stage2ContractsMin img ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr recordDeserializeName)
      (sessDeserializeSpec scopeKit E2E.HooksE.A0 img) := by
  have hCallees := Proofs.libsignal.Hooks2.deserializeCalleesAtW_of_stage2Min hStage2
  exact Symbolic.Swarm.TRREF.B3DeserQ.deserializeBodyQW_ok img ext
    (Symbolic.Swarm.TRREF.B3DeserQ.deserLeavesQW_of_contractsMin img ext hCallees hStage2)
    (Symbolic.Swarm.TRREF.B3DeserQ.mergeFieldQW_ok img ext hStage2.loads hCallees)

theorem sessDeserialize_of_sub_scopeKit_ok {img : Obj.Image}
    {ext : String → Option (State → State)}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hStage2 : Proofs.libsignal.Hooks2.Stage2ContractsMin img ext)
    (hsub : ∀ r, Scope r → scopeKit r) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr recordDeserializeName)
      (sessDeserializeSpec Scope E2E.HooksE.A0 img) := by
  refine subroutine_ok_map_panic (sessDeserialize_scopeKit_ok hStage2) fun x R s0 hpre => ?_
  refine ⟨x, R, ?_, fun _ h => h, fun _ h => h⟩
  dsimp only [sessDeserializeSpec] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
  obtain ⟨⟨hx0, hx1, hx8, hsc, hF, hsym⟩, hmem⟩ := hpre
  exact ⟨⟨hx0, hx1, hx8, hsub x.r hsc, hF, hsym⟩, hmem⟩

theorem sessDeserialize_scopeKit_trTrap {img : Obj.Image} (W : CliHooks)
    (himg : Obj.Loads libsignalSessionImage img) :
    subroutine_ok (tripleRatchetProgAtExt img.base (trTrapExterns W.C (cliExterns W)))
      ((tripleRatchetProgAtExt img.base (trTrapExterns W.C (cliExterns W))).fnAddr
        recordDeserializeName)
      (sessDeserializeSpec scopeKit E2E.HooksE.A0 img) :=
  sessDeserialize_scopeKit_ok (stage2ContractsMin_trTrap W himg)

theorem sessDeserialize_scopeKit_cli {img : Obj.Image} (W : CliHooks)
    (himg : Obj.Loads libsignalSessionImage img) :
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExterns W))
      ((tripleRatchetProgAtExt img.base (cliExterns W)).fnAddr recordDeserializeName)
      (sessDeserializeSpec scopeKit E2E.HooksE.A0 img) :=
  subroutine_ok_cli_of_trTrap (sessDeserialize_scopeKit_trTrap W himg)

alias cliExterns_sessDeserialize_scopeKit := sessDeserialize_scopeKit_cli

theorem cliExterns_sessDeserialize_of_sub_scopeKit {img : Obj.Image} (W : CliHooks)
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (himg : Obj.Loads libsignalSessionImage img) (hsub : ∀ r, Scope r → scopeKit r) :
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExterns W))
      ((tripleRatchetProgAtExt img.base (cliExterns W)).fnAddr recordDeserializeName)
      (sessDeserializeSpec Scope E2E.HooksE.A0 img) :=
  subroutine_ok_cli_of_trTrap
    (sessDeserialize_of_sub_scopeKit_ok (stage2ContractsMin_trTrap W himg) hsub)

private theorem rngTrap_fsT : HookFsTraced RunGlue.IsFsC rngTrap :=
  fun _ => FsTraced.of_eq rfl rfl

theorem fsTHooks_withPanics_trTrap (W : CliHooks) :
    RunGlue.FsTHooks (Rust.withPanics (trTrapExterns W.C (cliExterns W))) := by
  intro n f h
  by_cases hr : n = rngFillName
  · subst hr
    unfold Rust.withPanics trTrapExterns ProofLib.Variant.trapAt at h
    split at h
    · cases h; exact RunGlue.panicked_fsT
    · simp only [beq_self_eq_true, ↓reduceIte, Option.some.injEq] at h
      subst h; exact rngTrap_fsT
  · rw [withPanics_trTrap_ne W.C (cliExterns W) hr, cliExterns_agree W 0#64 hr] at h
    exact RunGlue.fsTHooks_withPanics (RunGlue.fsTHooks_cliExterns W) n f h

theorem traceFsSound_trTrap (W : CliHooks) (b : BitVec 64) :
    TraceFsSound (tripleRatchetProgAtExt b (trTrapExterns W.C (cliExterns W))) :=
  RunGlue.traceFsSound_of_fsTHooks (fsTHooks_withPanics_trTrap W) RunGlue.fsTHooks_none

/-- `RunHooks` on `trTrapExterns W.C (cliExterns W)` at `E2E.HooksE.A0`. -/
theorem RunHooks.trTrap (W : CliHooks) (img : Obj.Image) :
    RunHooks img E2E.HooksE.A0 (trTrapExterns W.C (cliExterns W)) where
  alloc := allocContractsX_trTrap W img
  allocFs := allocContractsFs_trTrap W img
  memcpyRO := hookSat_trTrap_of_cli W (by decide)
    (by simp [Rust.isPanicSymbol, memcpyName]) (cli_hookSat_memcpy_region_ro W)
  bcmp := hookSat_trTrap_of_cli W (by decide)
    (by simp [Rust.isPanicSymbol, cliBcmpName]) (RunGlue.cli_hookSat_bcmp W)
  fs := traceFsSound_trTrap W img.base
  utf8 :=
    let ⟨err, herr⟩ := (RunHooks.cli W img).utf8
    ⟨err, (trTrapExterns_cli_eq W (by decide) (by simp [Rust.isPanicSymbol])).trans herr⟩
  memrchr :=
    (trTrapExterns_cli_eq W (by decide) (by simp [Rust.isPanicSymbol])).trans
      (cliExterns_memrchr W)
  allocHooks :=
    let hA := cliExterns_allocHooks W
    ⟨hookSat_trTrap_of_cli W (by decide) (by simp [Rust.isPanicSymbol]) hA.alloc,
     hookSat_trTrap_of_cli W (by decide) (by simp [Rust.isPanicSymbol]) hA.dealloc,
     hookSat_trTrap_of_cli W (by decide) (by simp [Rust.isPanicSymbol]) hA.realloc⟩
  allocZeroed := hookSat_trTrap_of_cli W (by decide)
    (by simp [Rust.isPanicSymbol, allocZeroedName]) (cliExterns_allocZeroed W)
  allocContracts := allocContracts_trTrap W img
  formatInner := hookSat_trTrap_of_cli W (by decide)
    (by simp [Rust.isPanicSymbol, formatInnerName]) (cliExterns_formatInner W)

theorem cliReadFile_ok_trTrap (W : CliHooks) (img : Obj.Image) (stk : Nat) :
    subroutine_ok (tripleRatchetProgAtExt img.base (trTrapExterns W.C (cliExterns W)))
      ((tripleRatchetProgAtExt img.base (trTrapExterns W.C (cliExterns W))).fnAddr Cli.readFileName)
      (readFileSpec cliIo.rd cliWrOk E2E.HooksE.A0 img stk) := by
  have hsat := hookSat_trTrap_of_cli W (by decide)
    (by simp [Rust.isPanicSymbol, Cli.readFileName])
    (RunSkeleton.cliReadFile_hookSat W img stk)
  have h := hook_ok_at (P := libsignalSessionCode) (b := img.base)
    (hooks := trTrapExterns W.C (cliExterns W))
    (hname := SignalSession.readFileName) (k := 0) Cli.readFile_fnOff (Nat.add_zero _) (by decide)
    (ls_hook% "libsignal_cli_io::read_file")
    (by simp [Rust.isPanicSymbol, SignalSession.readFileName]) hsat
  simpa only [tripleRatchetProgAtExt, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using h

theorem serializeCanonX_trTrap (W : CliHooks) (img : Obj.Image) :
    subroutine_ok (tripleRatchetProgAtExt img.base (trTrapExterns W.C (cliExterns W)))
      ((tripleRatchetProgAtExt img.base (trTrapExterns W.C (cliExterns W))).fnAddr
        CryptoVerification.SignalSession.Cli.recordSerializeName)
      ((Proofs.libsignal.Hooks2.serializeCanonSpecX E2E.HooksE.A0).inImage img) :=
  Store.SerGlueX.serializeCanonX_ok_of_trAllocContractsX (allocContractsX_trTrap W img)

theorem trTrapExterns_blackBox (W : CliHooks) :
    Rust.withPanics (trTrapExterns W.C (cliExterns W)) "subtle::black_box::<u8>" =
      some CryptoVerification.LibsignalSession.blackBoxHook := by
  have hne : ("subtle::black_box::<u8>" : String) ≠ rngFillName := by decide
  rw [withPanics_trTrap_ne W.C (cliExterns W) hne, cliExterns_agree W 0#64 hne]
  exact KitInst.cliExterns_blackBox W

/-- `SessionOnlyKitOkSE` on `cliExterns W` at `Scope := scopeKit`. -/
theorem cliSessKitOkSE_scopeKit_cli (W : CliHooks) {img : Obj.Image} {F0 : FsFiles}
    {peer : AddrGhost} {readStk s1 s2 s3 s4 : Nat}
    (himg : Obj.Loads libsignalSessionImage img)
    (hs1 : loadShimNeed ≤ s1) (hs2 : loadPollNeed readStk ≤ s2)
    (hs3 : storeShimNeed ≤ s3) (hs4 : storePollNeedX ≤ s4) :
    MessageDecrypt.SessionOnlyKitOkSE
      (cliSessionStoreSpec E2E.HooksE.A0 img.base cliIo.rd F0 cliWrOk scopeKit peer s1 s2 s3 s4)
      scopeKit E2E.Record.encodeRecord (cliExterns W) :=
  cliSessKitOkSE_cli W himg (sessDeserialize_scopeKit_cli W himg) hs1 hs2 hs3 hs4

/-- `SessionOnlyKitOkSE` on `trTrapExterns W.C (cliExterns W)` at `E2E.HooksE.A0`. -/
theorem cliSessKitOkSE_trTrap (W : CliHooks) {img : Obj.Image} {F0 : FsFiles}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {peer : AddrGhost}
    {readStk s1 s2 s3 s4 : Nat}
    (himg : Obj.Loads libsignalSessionImage img)
    (hDeser : subroutine_ok (tripleRatchetProgAtExt img.base (trTrapExterns W.C (cliExterns W)))
      ((tripleRatchetProgAtExt img.base (trTrapExterns W.C (cliExterns W))).fnAddr
        recordDeserializeName)
      (sessDeserializeSpec Scope E2E.HooksE.A0 img))
    (hs1 : loadShimNeed ≤ s1) (hs2 : loadPollNeed readStk ≤ s2)
    (hs3 : storeShimNeed ≤ s3) (hs4 : storePollNeedX ≤ s4) :
    MessageDecrypt.SessionOnlyKitOkSE
      (cliSessionStoreSpec E2E.HooksE.A0 img.base cliIo.rd F0 cliWrOk Scope peer s1 s2 s3 s4)
      Scope E2E.Record.encodeRecord (trTrapExterns W.C (cliExterns W)) :=
  cliSessKitOkSE himg (RunHooks.trTrap W img) (cliReadFile_ok_trTrap W img readStk)
    hDeser (serializeCanonX_trTrap W img) hs1 hs2 hs3 hs4

theorem cliSessKitOkSE_scopeKit_trTrap (W : CliHooks) {img : Obj.Image} {F0 : FsFiles}
    {peer : AddrGhost} {readStk s1 s2 s3 s4 : Nat}
    (himg : Obj.Loads libsignalSessionImage img)
    (hs1 : loadShimNeed ≤ s1) (hs2 : loadPollNeed readStk ≤ s2)
    (hs3 : storeShimNeed ≤ s3) (hs4 : storePollNeedX ≤ s4) :
    MessageDecrypt.SessionOnlyKitOkSE
      (cliSessionStoreSpec E2E.HooksE.A0 img.base cliIo.rd F0 cliWrOk scopeKit peer s1 s2 s3 s4)
      scopeKit E2E.Record.encodeRecord (trTrapExterns W.C (cliExterns W)) :=
  cliSessKitOkSE_trTrap W himg (sessDeserialize_scopeKit_trTrap W himg) hs1 hs2 hs3 hs4

/-- Transfers `SessionOnlyKitOkSE` from `trTrapExterns C abs` to `SessionOnlyKitOkS` on `tripleRatchetProgAt img.base C ctl abs`. -/
theorem sessionOnlyKitOkS_of_trTrap {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    (ctl : BitVec 64) {abs : String → Option (State → State)}
    (h : MessageDecrypt.SessionOnlyKitOkSE kit Scope encRecord (trTrapExterns C abs)) :
    MessageDecrypt.SessionOnlyKitOkS kit Scope C encRecord ctl abs :=
  ⟨subroutine_ok_kit_of_trTrap h.loadShim,
   subroutine_ok_kit_of_trTrap h.loadPoll,
   subroutine_ok_kit_of_trTrap h.loadFutDrop,
   subroutine_ok_kit_of_trTrap h.storeShim,
   subroutine_ok_kit_of_trTrap h.storePoll,
   subroutine_ok_kit_of_trTrap h.storeFutDrop⟩

theorem cliSessKitOkS_scopeKit_kit (W : CliHooks) (ctl : BitVec 64) {img : Obj.Image}
    {F0 : FsFiles} {peer : AddrGhost} {readStk s1 s2 s3 s4 : Nat}
    (himg : Obj.Loads libsignalSessionImage img)
    (hs1 : loadShimNeed ≤ s1) (hs2 : loadPollNeed readStk ≤ s2)
    (hs3 : storeShimNeed ≤ s3) (hs4 : storePollNeedX ≤ s4) :
    MessageDecrypt.SessionOnlyKitOkS
      (cliSessionStoreSpec E2E.HooksE.A0 img.base cliIo.rd F0 cliWrOk scopeKit peer s1 s2 s3 s4)
      scopeKit W.C E2E.Record.encodeRecord ctl (cliExterns W) :=
  sessionOnlyKitOkS_of_trTrap ctl (cliSessKitOkSE_scopeKit_trTrap W himg hs1 hs2 hs3 hs4)

theorem cliSessKitOkS_scopeKit_trTrap (W : CliHooks) (ctl : BitVec 64) {img : Obj.Image}
    {F0 : FsFiles} {peer : AddrGhost} {readStk s1 s2 s3 s4 : Nat}
    (himg : Obj.Loads libsignalSessionImage img)
    (hs1 : loadShimNeed ≤ s1) (hs2 : loadPollNeed readStk ≤ s2)
    (hs3 : storeShimNeed ≤ s3) (hs4 : storePollNeedX ≤ s4) :
    MessageDecrypt.SessionOnlyKitOkS
      (cliSessionStoreSpec E2E.HooksE.A0 img.base cliIo.rd F0 cliWrOk scopeKit peer s1 s2 s3 s4)
      scopeKit W.C E2E.Record.encodeRecord ctl (trTrapExterns W.C (cliExterns W)) :=
  sessionOnlyKitOkS_of_trTrap ctl <|
    (trTrapExterns_idem W.C (cliExterns W)).symm ▸
      cliSessKitOkSE_scopeKit_trTrap W himg hs1 hs2 hs3 hs4

/-- `IdentityStoreKitOkIE` on `trTrapExterns W.C (cliExterns W)` at `E2E.HooksE.A0`. -/
theorem cliIdKitOkIE_trTrap (W : CliHooks) {img : Obj.Image} {F0 : FsFiles} {peer : AddrGhost}
    {readStk s1 s2 s3 s4 : Nat}
    (himg : Obj.Loads libsignalSessionImage img)
    (hs1 : trustShimNeed ≤ s1) (hs2 : trustPollNeed readStk ≤ s2)
    (hs3 : saveShimNeed ≤ s3) (hs4 : savePollNeed readStk ≤ s4) :
    StoreKit.Identity.IdentityStoreKitOkIE img
      (cliIdentityStoreSpec E2E.HooksE.A0 img.base cliIo.rd F0 cliWrOk peer s1 s2 s3 s4)
      (trTrapExterns W.C (cliExterns W)) :=
  cliIdKitOkIE himg (RunHooks.trTrap W img) (cliReadFile_ok_trTrap W img readStk)
    (Glue.publicKeyEq_ok_ext img.base (trTrapExterns_blackBox W)) hs1 hs2 hs3 hs4

/-- Transfers `IdentityStoreKitOkIE` from `trTrapExterns C abs` to `IdentityStoreKitOkI` on `tripleRatchetProgAt b C ctl abs`. -/
theorem identityStoreKitOkI_of_trTrap {A : RustAlloc} {b : BitVec 64} {img : Obj.Image}
    {ikit : IdentityStoreSpec A b} {C : Crypto} (ctl : BitVec 64)
    {abs : String → Option (State → State)}
    (h : StoreKit.Identity.IdentityStoreKitOkIE img ikit (trTrapExterns C abs)) :
    StoreKit.Identity.IdentityStoreKitOkI img ikit C ctl abs :=
  ⟨subroutine_ok_kit_of_trTrap h.trustShim,
   subroutine_ok_kit_of_trTrap h.trustPoll,
   subroutine_ok_kit_of_trTrap h.trustFutDrop,
   subroutine_ok_kit_of_trTrap h.saveShim,
   subroutine_ok_kit_of_trTrap h.savePoll,
   subroutine_ok_kit_of_trTrap h.saveFutDrop⟩

theorem cliIdKitOkI_kit (W : CliHooks) (ctl : BitVec 64) {img : Obj.Image} {F0 : FsFiles}
    {peer : AddrGhost} {readStk s1 s2 s3 s4 : Nat}
    (himg : Obj.Loads libsignalSessionImage img)
    (hs1 : trustShimNeed ≤ s1) (hs2 : trustPollNeed readStk ≤ s2)
    (hs3 : saveShimNeed ≤ s3) (hs4 : savePollNeed readStk ≤ s4) :
    StoreKit.Identity.IdentityStoreKitOkI img
      (cliIdentityStoreSpec E2E.HooksE.A0 img.base cliIo.rd F0 cliWrOk peer s1 s2 s3 s4)
      W.C ctl (cliExterns W) :=
  identityStoreKitOkI_of_trTrap ctl (cliIdKitOkIE_trTrap W himg hs1 hs2 hs3 hs4)

theorem cliIdKitOkI_trTrap (W : CliHooks) (ctl : BitVec 64) {img : Obj.Image} {F0 : FsFiles}
    {peer : AddrGhost} {readStk s1 s2 s3 s4 : Nat}
    (himg : Obj.Loads libsignalSessionImage img)
    (hs1 : trustShimNeed ≤ s1) (hs2 : trustPollNeed readStk ≤ s2)
    (hs3 : saveShimNeed ≤ s3) (hs4 : savePollNeed readStk ≤ s4) :
    StoreKit.Identity.IdentityStoreKitOkI img
      (cliIdentityStoreSpec E2E.HooksE.A0 img.base cliIo.rd F0 cliWrOk peer s1 s2 s3 s4)
      W.C ctl (trTrapExterns W.C (cliExterns W)) :=
  identityStoreKitOkI_of_trTrap ctl <|
    (trTrapExterns_idem W.C (cliExterns W)).symm ▸
      cliIdKitOkIE_trTrap W himg hs1 hs2 hs3 hs4

/-! ## 5. Contract-backed (`CliExternsOk P A ext`) kit and deserialization glue -/

section ExtKitGlue

theorem stage2ContractsMin_of_allocX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (himg : Obj.Loads libsignalSessionImage img)
    (hA : AllocContractsX img A ext) :
    Proofs.libsignal.Hooks2.Stage2ContractsMinExt img A ext :=
  Proofs.libsignal.Hooks2.Stage2ContractsMinExt.of_trAllocContractsX himg hA

theorem stage2ContractsMin_ext {P : E2E.PEParams} {A : RustAlloc} {ext : String → Option (State → State)}
    {img : Obj.Image} (hOk : CliExternsOk P A ext) (himg : Obj.Loads libsignalSessionImage img) :
    Proofs.libsignal.Hooks2.Stage2ContractsMinExt img A (cliExternsWith ext) :=
  stage2ContractsMin_of_allocX himg (MainHops.AllocContractsX.of_externsOk hOk img)

theorem sessDeserialize_scopeKit_ok_ext {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hStage2 : Proofs.libsignal.Hooks2.Stage2ContractsMinExt img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr recordDeserializeName) (sessDeserializeExtSpec scopeKit A img) := by
  have hCallees : Proofs.libsignal.Hooks2.DeserializeCalleesAtWA img A ext :=
    Proofs.libsignal.Hooks2.deserializeCalleesAtMinA_of_stage2MinExt hStage2
  have hLeaves : Symbolic.Swarm.TRREF.B3DeserQ.DeserLeavesQWA img A ext :=
    ⟨Symbolic.Swarm.TRREF.B3DeserQ.deserLoopEntryQ_ok_atWA img A ext hCallees,
     Symbolic.Swarm.TRREF.B3DeserQ.deserLoopIterQ_ok_atWA img A ext,
     Symbolic.Swarm.TRREF.B3DeserQ.deserLoopExitQ_ok_of_memcpyA img A ext
       (Proofs.libsignal.Hooks2.memcpy_ok_extWMinExt hStage2)⟩
  exact Symbolic.Swarm.TRREF.B3DeserQ.deserializeBodyQWA_ok img A ext hLeaves
    (Symbolic.Swarm.TRREF.B3DeserQ.mergeFieldQWA_ok img A ext hStage2.loads hCallees)

theorem sessDeserialize_of_sub_scopeKit_ok_ext {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hStage2 : Proofs.libsignal.Hooks2.Stage2ContractsMinExt img A ext) (hsub : ∀ r, Scope r → scopeKit r) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr recordDeserializeName) (sessDeserializeExtSpec Scope A img) :=
  subroutine_ok_sessDeserializeExtSpec_of_sub (sessDeserialize_scopeKit_ok_ext hStage2) hsub

theorem sessDeserialize_scopeKit_ext {P : E2E.PEParams} {A : RustAlloc} {ext : String → Option (State → State)}
    {img : Obj.Image} (hOk : CliExternsOk P A ext) (himg : Obj.Loads libsignalSessionImage img) :
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr recordDeserializeName)
      (sessDeserializeExtSpec scopeKit A img) :=
  sessDeserialize_scopeKit_ok_ext (stage2ContractsMin_ext hOk himg)

theorem sessDeserialize_of_sub_scopeKit_ext {P : E2E.PEParams} {A : RustAlloc} {ext : String → Option (State → State)}
    {img : Obj.Image} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hOk : CliExternsOk P A ext) (himg : Obj.Loads libsignalSessionImage img) (hsub : ∀ r, Scope r → scopeKit r) :
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr recordDeserializeName)
      (sessDeserializeExtSpec Scope A img) :=
  subroutine_ok_sessDeserializeExtSpec_of_sub (sessDeserialize_scopeKit_ext hOk himg) hsub

theorem cliSessKitOkSE_scopeKit_ext {P : E2E.PEParams} {A : RustAlloc} {ext : String → Option (State → State)}
    {img : Obj.Image} {F0 : FsFiles} {peer : AddrGhost} {readStk s1 s2 s3 s4 : Nat}
    (hOk : CliExternsOk P A ext) (himg : Obj.Loads libsignalSessionImage img)
    (hs1 : loadShimNeed ≤ s1) (hs2 : loadPollNeed readStk ≤ s2) (hs3 : storeShimNeed ≤ s3)
    (hs4 : storePollNeedX ≤ s4) (hreadStk : extHookStack ≤ readStk := by decide) :
    MessageDecrypt.SessionOnlyKitOkSE
      (cliSessionStoreSpec A img.base cliIo.rd F0 cliWrOk scopeKit peer s1 s2 s3 s4)
      scopeKit E2E.Record.encodeRecord (cliExternsWith ext) :=
  SessKit.cliSessKitOkSE_ext hOk himg (sessDeserialize_scopeKit_ext hOk himg) hs1 hs2 hs3 hs4 hreadStk

export CryptoVerification.SignalSession.Cli.KitInst.SessKit (cliSessKitOkSE_ext)
export CryptoVerification.SignalSession.Cli.KitInst.IdKit (cliIdKitOkIE_ext)
export CryptoVerification.SignalSession.Cli.Store.SerGlueX (serializeCanonX_ext)

end ExtKitGlue

end CryptoVerification.SignalSession.Cli.Slots
