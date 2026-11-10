/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs
public import LibsignalBinary.Proofs.PeakBudget.RealMainBinaryEnvAdapterD3
public import LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift
public import LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds
public import LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkSlot
public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.D3NonCanonValidOverAuxPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H7OverD3SlotDom0LeafL23
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.AgreePathACore
public import LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget

/-!
# `OverD3` Loaded-Session and Fresh-Responder Domain Bounds

Establishes `TopStateTight`, `SessionCloneDom 286196`, and the `2 MiB` serialized record bound for
sessions loaded under `CliPqOrD3RecvDom`, together with `TopStateTight`, `SessionCloneDom 16384`,
`W4TryDecryptPathACDomCmkOf`, and `FreshBobCloneDom 16384` on fresh-responder `pathAInitState` and
`pathAInitSession`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H7OverD3SlotDom0LeafL45R

open Arm64.Process (bytesOfString)
open CryptoGames.HKDF (bytesToKey32)
open CryptoGames.LibsignalSession (SessionState initializeRecipientSession)
open CryptoGames.LibsignalSessionApi (Session SessionRecord)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over (clearPending)
open CryptoVerification.E2E
  (LocalIdentity PEParams PreKeyMessageFields ResponderPreKeySecrets djbKey ofU8)
open CryptoVerification.E2E.Record (encodeRecord)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.LibsignalPublicApiRepr (RecordGhost)
open CryptoVerification.LibsignalSpqrV1 (spqrV1Init)
open CryptoVerification.LibsignalTripleRatchet (SeedsLen32)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost SessionGhost uuidTryParse)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SignalSession (Inputs)
open CryptoVerification.SignalSession.Cli (StoresGhost)
open CryptoVerification.SignalSession.Cli.KitInst (cliSessionStoreSpec)
open CryptoVerification.SignalSession.Cli.MainHops (AddrV cliIo cliWrOk parseArgs)
open CryptoVerification.SignalSession.Cli.RunCompose (addrValOf runFiles)
open CryptoVerification.SignalSession.Cli.RunProofs.Poll
  (cliKitStk cliPollSessKitPlaced pathAInitSession pathAInitSession_scopeIn pathAInitState)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots (scopeKit)
open LibsignalBinary.Heap (AllocEvent)
open LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs (W4CloneACDomEnv)
open LibsignalBinary.Proofs.PeakBudget.RealMainBinaryEnvAdapterD3
  (CliPqOrD3RecvDom peerSpqrStateTight640_of_pqOrD3Recv)
open LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux
  (msgCapBytes sessionCapBytes spqrStateTightCapBytes)
open LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift
  (PeerSpqrStateTight640 peerSpqrStateTight640_of_cliSessionStoreSpec)
open LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLiftAux
  (TopStateTight topStateTight_length_le topStateTight_spqrV1Init)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds
  (FreshBobCloneDom RecordGhostValid SessionCloneDom sessionCloneDom_of_scopeKit_pq)
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkSlot
  (W4TryDecryptCallCmk W4TryDecryptPathACDomCmkOf)
open LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget (SessionGhostValid)
open LibsignalBinary.Proofs.SignalSession.Cli.D3 (spqrV1Init_length_le_2048)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H7OverD3SlotDom0LeafL23
  (h7l23_loadRel_encodeRecord_le_sessionCap_of_loadRel)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (SegCloneEnv)
open SignalPqxdh (DRKey)

/-! ## 1. Statements -/

/-- Under `CliPqOrD3RecvDom P i`, `parseArgs = some (.recv peerV)`, `F = runFiles i`,
`peer.val = addrValOf peerV`, and a `cliPollSessKitPlaced` session load returning `r` with
`r.currentSession = some s_old`, `s_old.state.pqRatchetState` satisfies `TopStateTight`, both
`s_old` and `clearPending s_old` satisfy `SessionCloneDom 286196`, and
`(encodeRecord r).length ≤ 2097152`. -/
def h7l4_Stmt : Prop :=
  ∀ [LibsignalPlacement] (A : RustAlloc) (P : PEParams) (B : RunBudgets)
    {i : Inputs} {peerV : AddrV} {F : FsFiles} {peer : AddrGhost}
    {r : SessionRecord (List (BitVec 8))} {s_old : Session (List (BitVec 8))},
    CliPqOrD3RecvDom P i →
    parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.recv peerV) →
    F = runFiles i →
    peer.val = addrValOf peerV →
    (cliPollSessKitPlaced A F scopeKit peer (cliKitStk B)).loadRel
      StoresGhost.opened.sessions peer.val (.ok (some r)) →
    r.currentSession = some s_old →
    TopStateTight P.C.F P.Q.K s_old.state.pqRatchetState ∧
    SessionCloneDom 286196 s_old ∧
    SessionCloneDom 286196 (clearPending s_old) ∧
    (encodeRecord r).length ≤ 2097152

/-- Fresh-responder `st0 := pathAInitState P me k m dk` (`ses0 := pathAInitSession P me k m dk`)
has `receiverChains = []`, `pqRatchetState.length ≤ 2048`, `TopStateTight`,
`SessionCloneDom 16384 ses0`, `W4TryDecryptPathACDomCmkOf P.C.F P.Q.K msgCapBytes` on calls with
`td.a.st = st0` and `td.a.msg.ciphertext.length ≤ msgCapBytes`, and — given
`SessionGhostValid recG ses0` — `FreshBobCloneDom 16384 recG ses0` and
`SegCloneEnv recG st0 ⊆ W4CloneACDomEnv`. -/
def h7l5a_Stmt : Prop :=
  ∀ (P : PEParams) (me : LocalIdentity) (k : ResponderPreKeySecrets)
    (m : PreKeyMessageFields) (dk : DRKey),
    let ses0 := pathAInitSession P me k m dk
    let st0 := pathAInitState P me k m dk
    st0.receiverChains = [] ∧
    st0.pqRatchetState.length ≤ 2048 ∧
    TopStateTight P.C.F P.Q.K st0.pqRatchetState ∧
    SessionCloneDom 16384 ses0 ∧
    (∀ (td : W4TryDecryptCallCmk),
      td.a.st = st0 →
      td.a.msg.ciphertext.length ≤ msgCapBytes →
      W4TryDecryptPathACDomCmkOf P.C.F P.Q.K msgCapBytes td) ∧
    (∀ (recG : SessionGhost),
      SessionGhostValid recG ses0 →
      FreshBobCloneDom 16384 recG ses0 ∧
      ∀ evs, SegCloneEnv recG st0 evs → W4CloneACDomEnv evs)

/-! ## 2. Loaded-Session Domain Bounds -/

private theorem h7l45r_scopeKit_of_loadRel [LibsignalPlacement]
    {A : RustAlloc} {F : FsFiles} {peer : AddrGhost} {B : RunBudgets}
    {r : SessionRecord (List (BitVec 8))}
    (hload : (cliPollSessKitPlaced A F scopeKit peer (cliKitStk B)).loadRel
      StoresGhost.opened.sessions peer.val (.ok (some r))) :
    scopeKit r := by
  obtain ⟨bs, _hget, hans⟩ := hload
  cases bs with
  | nil => cases hans
  | cons _ _ =>
    obtain ⟨r', hr', _henc, hsc⟩ := hans
    injection hr' with hr'
    injection hr' with hr'
    subst hr'
    exact hsc

private theorem h7l45r_seedsLen32_clearPending {s : Session (List (BitVec 8))}
    (h : SeedsLen32 s.state) :
    SeedsLen32 (clearPending s).state := by
  simpa [clearPending, SeedsLen32] using h

/-- `clearPending` preserves `SessionCloneDom pqCap` (drops `pendingKyberPreKey` to `none` and only
clears `pendingPreKey := false` inside `state`). -/
theorem h7l45r_sessionCloneDom_clearPending {pqCap : Nat}
    {s : Session (List (BitVec 8))}
    (hdom : SessionCloneDom pqCap s) :
    SessionCloneDom pqCap (clearPending s) where
  rc_len := hdom.rc_len
  seeds32 := h7l45r_seedsLen32_clearPending hdom.seeds32
  alice_len := hdom.alice_len
  kyber_cap := fun _ hk => nomatch hk
  pq_len := hdom.pq_len

theorem h7l45r_loaded_session_tight_and_cloneDom [LibsignalPlacement]
    (A : RustAlloc) (P : PEParams) (B : RunBudgets)
    {i : Inputs} {peerV : AddrV} {F : FsFiles} {peer : AddrGhost}
    {r : SessionRecord (List (BitVec 8))} {s_old : Session (List (BitVec 8))}
    (hi : CliPqOrD3RecvDom P i)
    (hparse : parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.recv peerV))
    (hfiles : F = runFiles i)
    (hpeer : peer.val = addrValOf peerV)
    (hload : (cliPollSessKitPlaced A F scopeKit peer (cliKitStk B)).loadRel
      StoresGhost.opened.sessions peer.val (.ok (some r)))
    (hcur : r.currentSession = some s_old) :
    TopStateTight P.C.F P.Q.K s_old.state.pqRatchetState ∧
    SessionCloneDom 286196 s_old ∧
    SessionCloneDom 286196 (clearPending s_old) ∧
    (encodeRecord r).length ≤ 2097152 := by
  have hPeer0 : PeerSpqrStateTight640 P.C.F P.Q.K (runFiles i) (addrValOf peerV) :=
    peerSpqrStateTight640_of_pqOrD3Recv hi hparse
  have hPeer : PeerSpqrStateTight640 P.C.F P.Q.K F peer.val := by
    rw [hfiles, hpeer]
    exact hPeer0
  have hKit : scopeKit r := h7l45r_scopeKit_of_loadRel hload
  let σ := cliKitStk B
  have hScAt :
      (cliSessionStoreSpec A 0#64 cliIo.rd F cliWrOk scopeKit peer
        σ.sessLoadShim σ.sessLoadPoll σ.sessStoreShim σ.sessStorePoll).ScopeAt
        scopeKit StoresGhost.opened.sessions peer.val r :=
    ⟨hKit, hload⟩
  have hTop : TopStateTight P.C.F P.Q.K s_old.state.pqRatchetState :=
    peerSpqrStateTight640_of_cliSessionStoreSpec hScAt hcur rfl hPeer
  have hpq_le : s_old.state.pqRatchetState.length ≤ 286196 := by
    have hle := topStateTight_length_le hTop
    have hcap_eq : spqrStateTightCapBytes = 286196 := rfl
    rw [hcap_eq] at hle
    exact hle
  have hDom : SessionCloneDom 286196 s_old :=
    sessionCloneDom_of_scopeKit_pq hKit hcur hpq_le
  have hDomClr : SessionCloneDom 286196 (clearPending s_old) :=
    h7l45r_sessionCloneDom_clearPending hDom
  have hEnc : (encodeRecord r).length ≤ 2097152 := by
    have hle := h7l23_loadRel_encodeRecord_le_sessionCap_of_loadRel hload
    have hcap_eq : sessionCapBytes = 2097152 := rfl
    rw [hcap_eq] at hle
    exact hle
  exact ⟨hTop, hDom, hDomClr, hEnc⟩

theorem h7l45r_l4 : h7l4_Stmt := by
  intro _ A P B _i _peerV _F _peer _r _s_old hi hparse hfiles hpeer hload hcur
  exact h7l45r_loaded_session_tight_and_cloneDom A P B hi hparse hfiles hpeer hload hcur

/-- Discharges `arch_valid` on `W4BinaryArchiveDirectEnv` via `g_arch := ⟨0#64, 0#64, none⟩`. -/
theorem h7l45r_arch_valid_none (r : SessionRecord (List (BitVec 8))) :
    ∀ (G : SessionGhost) (ses : Session (List (BitVec 8))),
      (⟨0#64, 0#64, none⟩ : RecordGhost).cur = some G →
      r.currentSession = some ses →
      SessionGhostValid G ses ∧ SessionCloneDom 286196 ses := by
  intro _ _ hg
  cases hg

/-- Discharges `arch_valid` given `RecordGhostValid g_arch r`, `r.currentSession = some s_old`, and `SessionCloneDom 286196 s_old`. -/
theorem h7l45r_arch_valid_some {g_arch : RecordGhost}
    {r : SessionRecord (List (BitVec 8))} {s_old : Session (List (BitVec 8))}
    (hcur : r.currentSession = some s_old)
    (hdom : SessionCloneDom 286196 s_old)
    (hrgv : RecordGhostValid g_arch r) :
    ∀ (G : SessionGhost) (ses : Session (List (BitVec 8))),
      g_arch.cur = some G →
      r.currentSession = some ses →
      SessionGhostValid G ses ∧ SessionCloneDom 286196 ses := by
  intro G ses hg hses
  have hs_eq : ses = s_old := Option.some.inj (hses.symm.trans hcur)
  subst hs_eq
  have hgv : SessionGhostValid G ses := by
    unfold RecordGhostValid at hrgv
    rw [hg, hses] at hrgv
    exact hrgv
  exact ⟨hgv, hdom⟩

/-! ## 3. Fresh-Responder `pathAInitState` and `pathAInitSession` Bounds -/

/-- `pathAInitState` has `receiverChains = []` (fresh recipient session before first decrypt). -/
theorem h7l45r_pathAInit_receiverChains_nil
    (P : PEParams) (me : LocalIdentity) (k : ResponderPreKeySecrets)
    (m : PreKeyMessageFields) (dk : DRKey) :
    (pathAInitState P me k m dk).receiverChains = [] := by
  simp [pathAInitState, initializeRecipientSession, SessionState.new, SessionState.setSenderChain]

theorem h7l45r_pathAInit_pqRatchetState_eq
    (P : PEParams) (me : LocalIdentity) (k : ResponderPreKeySecrets)
    (m : PreKeyMessageFields) (dk : DRKey) :
    (pathAInitState P me k m dk).pqRatchetState =
      spqrV1Init P.C.F P.Q.K .b2a (bytesToKey32 (ofU8 dk.pqrKey)) :=
  rfl

theorem h7l45r_pathAInit_pqRatchetState_length_le_2048
    (P : PEParams) (me : LocalIdentity) (k : ResponderPreKeySecrets)
    (m : PreKeyMessageFields) (dk : DRKey) :
    (pathAInitState P me k m dk).pqRatchetState.length ≤ 2048 := by
  rw [h7l45r_pathAInit_pqRatchetState_eq]
  exact spqrV1Init_length_le_2048 P.C.F P.Q.K .b2a (bytesToKey32 (ofU8 dk.pqrKey))

/-- `TopStateTight` on fresh-responder `pathAInitState`. -/
theorem h7l45r_pathAInit_topStateTight
    (P : PEParams) (me : LocalIdentity) (k : ResponderPreKeySecrets)
    (m : PreKeyMessageFields) (dk : DRKey) :
    TopStateTight P.C.F P.Q.K (pathAInitState P me k m dk).pqRatchetState := by
  rw [h7l45r_pathAInit_pqRatchetState_eq]
  exact topStateTight_spqrV1Init P.C.F P.Q.K .b2a (bytesToKey32 (ofU8 dk.pqrKey))

/-- `SessionCloneDom 16384` on fresh-responder `pathAInitSession`. -/
theorem h7l45r_pathAInit_sessionCloneDom_16K
    (P : PEParams) (me : LocalIdentity) (k : ResponderPreKeySecrets)
    (m : PreKeyMessageFields) (dk : DRKey) :
    SessionCloneDom 16384 (pathAInitSession P me k m dk) := by
  obtain ⟨_hIn0, _hver4, hSeeds, _hRC, _hPqLt⟩ := pathAInitSession_scopeIn P me k m dk
  have hrc0 : (pathAInitSession P me k m dk).state.receiverChains = [] :=
    h7l45r_pathAInit_receiverChains_nil P me k m dk
  have hpq2048 : (pathAInitSession P me k m dk).state.pqRatchetState.length ≤ 2048 :=
    h7l45r_pathAInit_pqRatchetState_length_le_2048 P me k m dk
  refine ⟨?_, hSeeds, ?_, ?_, Nat.le_trans hpq2048 (by decide)⟩
  · rw [hrc0]
    decide
  · simp [pathAInitSession, djbKey]
  · intro _ hk
    cases hk

/-- `W4TryDecryptPathACDomCmkOf P.C.F P.Q.K maxCt` for any `W4TryDecryptCallCmk` at
`pathAInitState P me k m dk` with ciphertext length `≤ maxCt`. -/
theorem h7l45r_pathAInit_tdAC_dom {maxCt : Nat}
    (P : PEParams) (me : LocalIdentity) (k : ResponderPreKeySecrets)
    (m : PreKeyMessageFields) (dk : DRKey)
    (td : W4TryDecryptCallCmk)
    (hst : td.a.st = pathAInitState P me k m dk)
    (hct : td.a.msg.ciphertext.length ≤ maxCt) :
    W4TryDecryptPathACDomCmkOf P.C.F P.Q.K maxCt td := by
  have hrc0 : td.a.st.receiverChains = [] := by
    rw [hst]
    exact h7l45r_pathAInit_receiverChains_nil P me k m dk
  have htop : TopStateTight P.C.F P.Q.K td.a.st.pqRatchetState := by
    rw [hst]
    exact h7l45r_pathAInit_topStateTight P me k m dk
  refine ⟨⟨?_, ?_, htop, hct⟩, hrc0⟩
  · rw [hrc0]
    decide
  · intro c hc
    rw [hrc0] at hc
    cases hc

theorem h7l45r_pathAInit_freshBobCloneDom
    (P : PEParams) (me : LocalIdentity) (k : ResponderPreKeySecrets)
    (m : PreKeyMessageFields) (dk : DRKey)
    (recG : SessionGhost)
    (hgv : SessionGhostValid recG (pathAInitSession P me k m dk)) :
    FreshBobCloneDom 16384 recG (pathAInitSession P me k m dk) where
  rc_nil := h7l45r_pathAInit_receiverChains_nil P me k m dk
  gv := hgv
  dom := h7l45r_pathAInit_sessionCloneDom_16K P me k m dk

/-- `SegCloneEnv recG st0 ⊆ W4CloneACDomEnv` given
`SessionGhostValid recG (pathAInitSession P me k m dk)`. -/
theorem h7l45r_pathAInit_segClone_sub_w4CloneACDomEnv
    (P : PEParams) (me : LocalIdentity) (k : ResponderPreKeySecrets)
    (m : PreKeyMessageFields) (dk : DRKey)
    (recG : SessionGhost)
    (hgv : SessionGhostValid recG (pathAInitSession P me k m dk))
    {evs : List AllocEvent}
    (hevs : SegCloneEnv recG (pathAInitState P me k m dk) evs) :
    W4CloneACDomEnv evs :=
  ⟨recG, pathAInitSession P me k m dk,
    h7l45r_pathAInit_freshBobCloneDom P me k m dk recG hgv, hevs⟩

theorem h7l45r_l5a : h7l5a_Stmt := by
  intro P me k m dk
  refine ⟨h7l45r_pathAInit_receiverChains_nil P me k m dk,
    h7l45r_pathAInit_pqRatchetState_length_le_2048 P me k m dk,
    h7l45r_pathAInit_topStateTight P me k m dk,
    h7l45r_pathAInit_sessionCloneDom_16K P me k m dk,
    fun td hst hct => h7l45r_pathAInit_tdAC_dom P me k m dk td hst hct,
    fun recG hgv => ⟨h7l45r_pathAInit_freshBobCloneDom P me k m dk recG hgv,
      fun _ hevs => h7l45r_pathAInit_segClone_sub_w4CloneACDomEnv P me k m dk recG hgv hevs⟩⟩

end LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H7OverD3SlotDom0LeafL45R
