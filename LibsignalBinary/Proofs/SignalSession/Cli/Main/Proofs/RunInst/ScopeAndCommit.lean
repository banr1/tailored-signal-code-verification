/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptSignal
import all Init.Data.Repr
import all Init.Data.ToString.Basic
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.StackBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Main.GamePaths
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.S0Proofs
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Refine.Plumbing
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.Oblig.EncSessionInj
import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSessionApiFacts

/-!
# Record Scope, Stack Budget, and `CommitOk` Helpers for `RunInst`

Proves `EncodeInjOn Slots.scopeIn`, session-record scope coverage for SM and PQXDH domains, the
concrete stack-budget bound `runNeed cliRunBudgets … ≤ cliResStack ≤ 2 ^ 63`, and `RunFilesOk`,
`RunEncOk`, `RunHsOk`, and `CommitOk` on SM and PQXDH domain inputs.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false

namespace CryptoVerification.SignalSession.Cli.MainHops

open Arm64 Arm64.Process ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunRefine
open CryptoVerification.SignalSession.Cli.RunProofs

/-! ## 1. Record scope obligations (`Slots.scopeIn` and `Slots.scopeKit`) -/

theorem encodeInjOn_scopeIn : Slots.EncodeInjOn Slots.scopeIn :=
  fun r₁ r₂ h₁ h₂ henc =>
    Slots.encodeInjOn_deserializeScopeP_Q r₁ r₂
      (Slots.scopeKit_of_scopeIn h₁) (Slots.scopeKit_of_scopeIn h₂) henc

theorem pqInV1_nil : Slots.PqValid.PqInV1 [] :=
  ⟨CryptoVerification.SpqrV1.Top.StateSize.validState_nil, by decide⟩

theorem scopeIn_of_deserializeScopeP {r : SessionRecord (List (BitVec 8))}
    (h : E2E.RecordX.DeserializeScopeP r) : Slots.scopeIn r :=
  ⟨⟨h.1.1, fun s hs => by rw [h.1.2.1 s hs]; exact pqInV1_nil, h.1.2.2⟩, h.2⟩

theorem ratchetScopeCoversSm_scopeIn (C : Crypto) :
    RatchetScopeCoversSm C Slots.scopeIn := by
  intro g hg
  have hd : E2E.Record.DeserializeGeneral.DeserializeScope
      (E2E.Record.toRecord E2E.Record.extrasM g) :=
    E2E.Reach.reach_deserializeScope C hg
  exact scopeIn_of_deserializeScopeP (E2E.RecordX.deserializeScopeP_of_deserializeScope hd)

theorem ratchetScopeCoversPq_scopeIn (W : PEParams) :
    RatchetScopeCoversPq W Slots.scopeIn := by
  intro st x g hwf hs
  have hwf_sess := hwf.1 x g hs
  rcases hwf_sess.1 with ⟨g₀, hr, _, hsess₀⟩
  have hlen31 := hwf_sess.2.2
  have hval : CryptoVerification.SpqrV1.Top.StateSize.ValidState g.session.pqRatchetState :=
    hsess₀ ▸ Slots.PqValid.reachPq_validState hr
  have hpq31 : g.session.pqRatchetState.length < 2 ^ 31 :=
    Nat.lt_of_le_of_lt (Slots.PqValid.pqRatchetState_length_le_encodeRecordX (fun _ => x) g) hlen31
  obtain ⟨hseeds₀, hrc₀, _, _, hrepr₀, _, hts, _, habk, hky⟩ := Slots.PqValid.reachPq_inv hr
  rw [hsess₀] at hseeds₀ hrc₀ hrepr₀
  rw [E2E.RecordX.toRecord_extrasOf_eq]
  refine ⟨⟨?_, ?_, ?_⟩, E2E.RecordX.sessionOfX (fun _ => x) g, rfl, ?_⟩
  · intro s hs'
    injection hs' with hs'
    subst hs'
    refine ⟨hseeds₀, Nat.lt_of_le_of_lt hrc₀ (by decide), ?_⟩
    intro k hk'
    unfold E2E.RecordX.sessionOfX at hk'
    dsimp only at hk'
    split at hk'
    · rw [hky k hk']; decide
    · cases hk'
  · intro s hs'
    injection hs' with hs'
    subst hs'
    exact ⟨hval, hpq31⟩
  · intro s hs'
    injection hs' with hs'
    subst hs'
    refine ⟨hrepr₀.1, hrepr₀.2, E2E.RecordX.sessionOfX_wf (fun _ => x) g, ?_⟩
    show x.aliceBaseKey.length < 2 ^ 32
    rw [habk]; decide
  · refine ⟨hrc₀, ?_, ?_, Or.inr habk⟩
    · intro p hp
      unfold E2E.RecordX.sessionOfX at hp
      dsimp only at hp
      split at hp
      · injection hp with hp'; subst hp'; exact hts
      · cases hp
    · intro k hk'
      unfold E2E.RecordX.sessionOfX at hk'
      dsimp only at hk'
      split at hk'
      · exact hky k hk'
      · cases hk'

/-! ## 2. Concrete budgets and stack reserve proof -/

/-- Concrete `RunBudgets` at `extHookStack` (`16384`). -/
def cliRunBudgets : RunBudgets := ⟨extHookStack⟩

/-- Concrete `RunNeeds` at `cliRunBudgets` with a parameterized `decryptPrekey` slot budget. -/
def cliRunNeeds (decPkNeed : Nat) : RunNeeds where
  encrypt := cliEncryptNeed cliRunBudgets
  decryptSignal := cliDecryptSignalNeed cliRunBudgets
  initiate := cliInitiateNeed cliRunBudgets
  decryptPrekey := decPkNeed

/-- Concrete `decryptPrekey` stack budget matching `DecryptPrekey/S0.lean`'s `cliDecryptPrekeyNeed`. -/
abbrev cliDecPkNeed₀ : Nat := 2144 + 1048576 + cliRunBudgets.dirGetNeed

theorem cliResStack_le_63 : cliResStack ≤ 2 ^ 63 := by
  decide

private theorem foldr_max_le {xs : List Nat} {acc b : Nat}
    (hacc : acc ≤ b) (hxs : ∀ x ∈ xs, x ≤ b) : xs.foldr max acc ≤ b := by
  induction xs with
  | nil => exact hacc
  | cons x xs ih =>
    simp only [List.foldr_cons, Nat.max_le]
    exact ⟨hxs x (List.mem_cons_self ..), ih (fun y hy => hxs y (List.mem_cons_of_mem x hy))⟩

theorem runNeed_cli_le_resStack {img : Obj.Image} {S : RunSem} {decPkNeed : Nat}
    (hdec : decPkNeed ≤ 4194304) :
    runNeed cliRunBudgets (slotsOf E2E.HooksE.A0 img S (cliRunNeeds decPkNeed)) ≤ cliResStack := by
  have hcallee :
      runCalleeNeed cliRunBudgets (slotsOf E2E.HooksE.A0 img S (cliRunNeeds decPkNeed)) ≤
        4194304 := by
    unfold runCalleeNeed
    refine foldr_max_le (by decide) fun x hx => ?_
    dsimp only [slotsOf, mkSlot, cliRunNeeds] at hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | exact hdec | decide
  have hsum : runFrame + 4194304 ≤ cliResStack := by decide
  unfold runNeed
  omega

/-- `runNeed_cli_le_resStack` generalized to an arbitrary allocator `A : RustAlloc`
(`(mkSlot spec need).need = need` ignores `spec`; proved directly via `foldr_max_le` to avoid
kernel unfolding of `slotsOf`). -/
theorem runNeed_cli_le_resStack_ext {A : RustAlloc} {img : Obj.Image} {S : RunSem}
    {decPkNeed : Nat} (hdec : decPkNeed ≤ 4194304) :
    runNeed cliRunBudgets (slotsOf A img S (cliRunNeeds decPkNeed)) ≤ cliResStack := by
  have hcallee :
      runCalleeNeed cliRunBudgets (slotsOf A img S (cliRunNeeds decPkNeed)) ≤ 4194304 := by
    unfold runCalleeNeed
    refine foldr_max_le (by decide) fun x hx => ?_
    dsimp only [slotsOf, mkSlot, cliRunNeeds] at hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | exact hdec | decide
  have hsum : runFrame + 4194304 ≤ cliResStack := by decide
  unfold runNeed
  omega

/-! ## 3. `RunFilesOk`, `RunEncOk`, and `RunHsOk` on SM and PQXDH domain inputs -/

theorem runFilesOk_smSend_cli {S : RunSem}
    (hS : S.filesOk = Slots.filesOk₀ Slots.scopeIn (fun _ => True))
    {C : Crypto} (g : GhostState (List (BitVec 8))) (m : List (BitVec 8))
    (hg : Reach (spqrOffSessionParams C) g) :
    RunFilesOk S (smSendInputs g m) :=
  Slots.runFilesOk_of_peer (.send (partyAddress g.party.other)) rfl rfl
    (ownAddr_smSend g m)
    (hS ▸ ⟨Slots.filesOkPeer_smSend g m (ratchetScopeCoversSm_scopeIn C g hg)
      (Slots.smSessBytes_le_fileCapBytes C hg),
      Slots.distinctSid_party g.party, trivial⟩)

theorem runFilesOk_smRecv_cli {S : RunSem}
    (hS : S.filesOk = Slots.filesOk₀ Slots.scopeIn (fun _ => True))
    {C : Crypto} (g : GhostState (List (BitVec 8))) (c : List (BitVec 8)) (rc : BitVec 256)
    (hg : Reach (spqrOffSessionParams C) g) :
    RunFilesOk S (smRecvInputs g c rc) :=
  Slots.runFilesOk_of_peer (.recv (partyAddress g.party.other)) rfl rfl
    (ownAddr_smRecv g c rc)
    (hS ▸ ⟨Slots.filesOkPeer_smRecv g c rc (ratchetScopeCoversSm_scopeIn C g hg)
      (Slots.smSessBytes_le_fileCapBytes C hg),
      Slots.distinctSid_party g.party, trivial⟩)

theorem runFilesOk_pqInit_cli {S : RunSem}
    (hS : S.filesOk = Slots.filesOk₀ Slots.scopeIn (fun _ => True))
    (W : PEParams) (st : PqParty) (b : PreKeyBundleFields) (t : List.Vector (BitVec 8) initiateTapeLen)
    (hwf : PqxdhPartyInSpecDomain W st) :
    RunFilesOk S (pqInitInputs W st b t) :=
  Slots.runFilesOk_of_peer (.init (partyAddress st.party.other) bundleDir) rfl rfl
    (ownAddr_pqInit W st b t)
    (hS ▸ ⟨Slots.filesOkPeer_pqInit W st b t
      (fun x g hs => ratchetScopeCoversPq_scopeIn W st x g hwf hs)
      (Slots.pqSessBytes_le_fileCapBytes hwf),
      Slots.distinctSid_party st.party, trivial⟩)

theorem runFilesOk_pqSend_cli {S : RunSem}
    (hS : S.filesOk = Slots.filesOk₀ Slots.scopeIn (fun _ => True))
    (W : PEParams) (st : PqParty) (m : List (BitVec 8)) (r : List.Vector (BitVec 8) 64)
    (hwf : PqxdhPartyInSpecDomain W st) :
    RunFilesOk S (pqSendInputs W st m r) :=
  Slots.runFilesOk_of_peer (.send (partyAddress st.party.other)) rfl rfl
    (ownAddr_pqSend W st m r)
    (hS ▸ ⟨Slots.filesOkPeer_pqSend W st m r
      (fun x g hs => ratchetScopeCoversPq_scopeIn W st x g hwf hs)
      (Slots.pqSessBytes_le_fileCapBytes hwf),
      Slots.distinctSid_party st.party, trivial⟩)

theorem runFilesOk_pqRecv_cli {S : RunSem}
    (hS : S.filesOk = Slots.filesOk₀ Slots.scopeIn (fun _ => True))
    (W : PEParams) (st : PqParty) (c : List (BitVec 8)) (rc : BitVec 256)
    (hwf : PqxdhPartyInSpecDomain W st) :
    RunFilesOk S (pqRecvInputs W st c rc) :=
  Slots.runFilesOk_of_peer (.recv (partyAddress st.party.other)) rfl rfl
    (ownAddr_pqRecv W st c rc)
    (hS ▸ ⟨Slots.filesOkPeer_pqRecv W st c rc
      (fun x g hs => ratchetScopeCoversPq_scopeIn W st x g hwf hs)
      (Slots.pqSessBytes_le_fileCapBytes hwf),
      Slots.distinctSid_party st.party, trivial⟩)

theorem runEncOk_smSend_cli {S : RunSem}
    (hS : S.encOk = Slots.encOk₀ Slots.scopeIn)
    {C : Crypto} (g : GhostState (List (BitVec 8))) (m : List (BitVec 8))
    (hg : Reach (spqrOffSessionParams C) g) :
    RunEncOk S (smSendInputs g m) :=
  Slots.runEncOk_smSend hS encodeInjOn_scopeIn g m
    (ratchetScopeCoversSm_scopeIn C g hg)
    (E2E.Reach.reach_pqRatchetState_eq_nil C hg)
    (Slots.smSessBytes_le_fileCapBytes C hg)

theorem runHsOk_smSend_cli (S : RunSem)
    (g : GhostState (List (BitVec 8))) (m : List (BitVec 8)) :
    RunHsOk S (smSendInputs g m) := by
  have ha : (smSendInputs g m).argv = (Cmd.send (partyAddress g.party.other)).argv := rfl
  refine ⟨fun peer dir _ _ h _ _ => ?_, fun peer _ _ _ _ h _ _ _ _ => ?_⟩
  · rw [ha, parseArgs_send] at h; cases h
  · rw [ha, parseArgs_send] at h; cases h

theorem runHsOk_smRecv_cli (S : RunSem)
    (g : GhostState (List (BitVec 8))) (c : List (BitVec 8)) (rc : BitVec 256) :
    RunHsOk S (smRecvInputs g c rc) := by
  have ha : (smRecvInputs g c rc).argv = (Cmd.recv (partyAddress g.party.other)).argv := rfl
  have hin : (smRecvInputs g c rc).stdin = 2#8 :: c := rfl
  refine ⟨fun peer dir _ _ h _ _ => ?_, fun peer _ _ rest _ h _ _ hstdin _ => ?_⟩
  · rw [ha, parseArgs_recv] at h; cases h
  · rw [hin] at hstdin; cases hstdin

theorem runHsOk_pqInit_cli {S : RunSem} {W : PEParams}
    (hS : S.initOk = InitOk₀ W)
    (st : PqParty) (b : PreKeyBundleFields) (t : List.Vector (BitVec 8) initiateTapeLen)
    (hwf : PqxdhPartyInSpecDomain W st) (hs : st.session = none) :
    RunHsOk S (pqInitInputs W st b t) := by
  have ha : (pqInitInputs W st b t).argv = (Cmd.init (partyAddress st.party.other) bundleDir).argv := rfl
  refine ⟨fun peer dir ownB meV hparse hown hme => ?_, fun peer _ _ _ _ h _ _ _ _ => ?_⟩
  · rw [ha, parseArgs_init] at hparse
    injection hparse with hc
    injection hc with hpeer _
    rw [ownAddr_pqInit] at hown
    injection hown with hown'
    subst hown'
    rw [addrParse_textBytes] at hme
    injection hme with hme'
    rw [← hpeer, ← hme', hS]
    exact InitS0.initOk₀_pqInit_proof W st b t hwf hs
  · rw [ha, parseArgs_init] at h; cases h

theorem runHsOk_pqSend_cli (S : RunSem)
    (W : PEParams) (st : PqParty) (m : List (BitVec 8)) (r : List.Vector (BitVec 8) 64) :
    RunHsOk S (pqSendInputs W st m r) := by
  have ha : (pqSendInputs W st m r).argv = (Cmd.send (partyAddress st.party.other)).argv := rfl
  refine ⟨fun peer dir _ _ h _ _ => ?_, fun peer _ _ _ _ h _ _ _ _ => ?_⟩
  · rw [ha, parseArgs_send] at h; cases h
  · rw [ha, parseArgs_send] at h; cases h

theorem runHsOk_pqRecvOther_cli (S : RunSem)
    (W : PEParams) (st : PqParty) (c : List (BitVec 8)) (rc : BitVec 256)
    (h3 : c.head? ≠ some wirePrekey) :
    RunHsOk S (pqRecvInputs W st c rc) := by
  have ha : (pqRecvInputs W st c rc).argv = (Cmd.recv (partyAddress st.party.other)).argv := rfl
  have hin : (pqRecvInputs W st c rc).stdin = c := rfl
  refine ⟨fun peer dir _ _ h _ _ => ?_, fun _ _ _ rest _ _ _ _ hstdin _ => ?_⟩
  · rw [ha, parseArgs_recv] at h; cases h
  · rw [hin] at hstdin
    subst hstdin
    exact absurd rfl h3

theorem runHsOk_pqRecvPrekey_of_decPkOk {S : RunSem}
    (W : PEParams) (st : PqParty) (m : PreKeyMessageFields) (rc : BitVec 256)
    (hdec : ∀ pm, S.pksmParse m.bytes = some pm →
      S.decPkOk (runFiles (pqRecvInputs W st (wirePrekey :: m.bytes) rc))
        (addrValE st.party.other) (addrValE st.party) pm) :
    RunHsOk S (pqRecvInputs W st (wirePrekey :: m.bytes) rc) := by
  have ha : (pqRecvInputs W st (wirePrekey :: m.bytes) rc).argv =
      (Cmd.recv (partyAddress st.party.other)).argv := rfl
  have hin : (pqRecvInputs W st (wirePrekey :: m.bytes) rc).stdin = wirePrekey :: m.bytes := rfl
  refine ⟨fun peer dir _ _ h _ _ => ?_, fun peer ownB meV rest pm hparse hown hme hstdin hpm => ?_⟩
  · rw [ha, parseArgs_recv] at h; cases h
  · rw [ha, parseArgs_recv] at hparse
    injection hparse with hc
    injection hc with hpeer
    rw [ownAddr_pqRecv] at hown
    injection hown with hown'
    subst hown'
    rw [addrParse_textBytes] at hme
    injection hme with hme'
    rw [hin] at hstdin
    injection hstdin with _ hrest
    subst hrest
    rw [← hpeer, ← hme']
    exact hdec pm hpm

/-! ## 4. `CommitOk` on SM and PQXDH domain answers (`initDef`, `encDef`, `decSigDef`) -/

private def kutf8Local (s : String) : List (BitVec 8) :=
  (s.toList.flatMap String.utf8EncodeChar).map fun b => BitVec.ofNat 8 b.toNat

private theorem byteArray_toList_eq_data_local : ∀ (bs : ByteArray), bs.toList = bs.data.toList
  | ⟨⟨xs⟩⟩ => by
    have hloop : ∀ i r, ByteArray.toList.loop ⟨⟨xs⟩⟩ i r = r.reverse ++ xs.drop i := by
      intro i r
      fun_induction ByteArray.toList.loop ⟨⟨xs⟩⟩ i r with
      | case1 i r hi ih =>
        have hi' : i < xs.length := hi
        have hget : (ByteArray.mk ⟨xs⟩).get! i = xs[i] := getElem!_pos (⟨xs⟩ : Array UInt8) i hi
        rw [ih, hget, List.reverse_cons, List.append_assoc, List.singleton_append,
          List.drop_eq_getElem_cons hi']
      | case2 i r hni =>
        rw [List.drop_eq_nil_of_le (Nat.le_of_not_lt hni), List.append_nil]
    exact hloop 0 []

private theorem utf8_eq_kutf8Local (s : String) : Cli.utf8 s = kutf8Local s := by
  obtain ⟨l, rfl⟩ := s.exists_eq_ofList
  simp [Cli.utf8, kutf8Local, List.utf8Encode, byteArray_toList_eq_data_local]

private theorem utf8_append_local (a b : String) : Cli.utf8 (a ++ b) = Cli.utf8 a ++ Cli.utf8 b := by
  rw [utf8_eq_kutf8Local, utf8_eq_kutf8Local, utf8_eq_kutf8Local]
  simp [kutf8Local, String.toList_append, List.flatMap_append]

private theorem pathOf_id_addrValE (P : Party) :
    Cli.pathOf (Cli.utf8 "identities") (addrValE P).name = Cli.utf8 (identityFile (partyAddressName P)) := by
  have hne : Cli.utf8 "identities" ≠ [] := by rw [utf8_eq_kutf8Local]; decide
  simp only [Cli.pathOf, hne, ↓reduceIte, addrValE, identityFile]
  rw [← utf8_append_local, ← utf8_append_local]
  rfl

private theorem pathOf_sess_addrValE (P : Party) :
    Cli.pathOf (Cli.utf8 "sessions") (Cli.addressText (addrValE P)) =
      Cli.utf8 (sessionFile (partyAddress P)) := by
  have hne : Cli.utf8 "sessions" ≠ [] := by rw [utf8_eq_kutf8Local]; decide
  have had : Cli.addressText (addrValE P) = Cli.utf8 (partyAddress P).text := by
    have h1 : (1#8 : BitVec 8).toNat = 1 := rfl
    simp only [Cli.addressText, addrValE, decimalText, h1, Address.text, partyAddress]
    rw [← utf8_append_local, ← utf8_append_local]
  rw [had]
  simp only [Cli.pathOf, hne, ↓reduceIte, sessionFile]
  rw [← utf8_append_local, ← utf8_append_local]
  rfl

private def okPeerPath (P : Party) (p : List (BitVec 8)) : Prop :=
  (∀ b ∈ p, b.toNat < 128) ∧
    (pathStr p = identityFile (partyAddressName P) ∨ pathStr p = sessionFile (partyAddress P))

private theorem okPeerPath_id (P : Party) :
    okPeerPath P (Cli.pathOf (Cli.utf8 "identities") (addrValE P).name) := by
  rw [pathOf_id_addrValE]
  refine ⟨?_, .inl ?_⟩
  · rw [utf8_eq_kutf8Local]
    intro b hb
    have hall :
        (kutf8Local (identityFile (partyAddressName P))).all (fun x => decide (x.toNat < 128)) = true := by
      cases P <;> rfl
    exact of_decide_eq_true (List.all_eq_true.mp hall b hb)
  · unfold pathStr; rw [utf8_eq_kutf8Local]; cases P <;> rfl

private theorem okPeerPath_sess (P : Party) :
    okPeerPath P (Cli.pathOf (Cli.utf8 "sessions") (Cli.addressText (addrValE P))) := by
  rw [pathOf_sess_addrValE]
  refine ⟨?_, .inr ?_⟩
  · rw [utf8_eq_kutf8Local]
    intro b hb
    have hall :
        (kutf8Local (sessionFile (partyAddress P))).all (fun x => decide (x.toNat < 128)) = true := by
      cases P <;> rfl
    exact of_decide_eq_true (List.all_eq_true.mp hall b hb)
  · unfold pathStr; rw [utf8_eq_kutf8Local]; cases P <;> rfl

def StoreCallPeer (peer : AddrVal) : StoreCall AddrVal (List (BitVec 8)) → Prop
  | .saveIdentity rem _ => rem = peer
  | .storeSession rem _ => rem = peer
  | _ => True

private theorem storesWrOk_cliStep {F : FsFiles} {P : Party} {g : StoresGhost}
    (hg : StoresWrOk (okPeerPath P) g) (hpeers : g.identity.peers.path = Cli.utf8 "identities")
    (hsess : g.sessions.path = Cli.utf8 "sessions")
    {c : StoreCall AddrVal (List (BitVec 8))} (hc : StoreCallPeer (addrValE P) c) :
    StoresWrOk (okPeerPath P) (cliStep F g c) ∧
      (cliStep F g c).identity.peers.path = Cli.utf8 "identities" ∧
      (cliStep F g c).sessions.path = Cli.utf8 "sessions" := by
  cases c with
  | loadSession _ => exact ⟨hg, hpeers, hsess⟩
  | isTrustedIdentity _ _ _ => exact ⟨hg, hpeers, hsess⟩
  | saveIdentity rem k =>
    simp only [StoreCallPeer] at hc
    subst hc
    dsimp only [cliStep]
    refine ⟨{ hg with
      own := by rw [saveUpd_own]; exact hg.own
      peers := DirWrOk.saveUpd hg.peers (hpeers ▸ okPeerPath_id P) }, ?_, hsess⟩
    rw [saveUpd_peers_path, hpeers]
  | storeSession rem r =>
    simp only [StoreCallPeer] at hc
    subst hc
    dsimp only [cliStep]
    exact ⟨{ hg with sessions := hg.sessions.put (hsess ▸ okPeerPath_sess P) _ }, hpeers, hsess⟩

private theorem storesWrOk_foldl {F : FsFiles} {P : Party} :
    ∀ (calls : List (StoreCall AddrVal (List (BitVec 8)))) (g : StoresGhost),
      (∀ c ∈ calls, StoreCallPeer (addrValE P) c) →
      StoresWrOk (okPeerPath P) g →
      g.identity.peers.path = Cli.utf8 "identities" →
      g.sessions.path = Cli.utf8 "sessions" →
      StoresWrOk (okPeerPath P) (calls.foldl (cliStep F) g)
  | [], _, _, hg, _, _ => hg
  | c :: cs, g, hc, hg, hp, hs =>
    let ⟨hg', hp', hs'⟩ := storesWrOk_cliStep hg hp hs (hc c (List.mem_cons_self ..))
    storesWrOk_foldl cs (cliStep F g c) (fun c' hc' => hc c' (List.mem_cons_of_mem c hc'))
      hg' hp' hs'

private theorem storesWrOk_cliFinal {F : FsFiles} {P : Party}
    (calls : List (StoreCall AddrVal (List (BitVec 8))))
    (hcalls : ∀ c ∈ calls, StoreCallPeer (addrValE P) c) :
    StoresWrOk (okPeerPath P) (cliFinal F calls) :=
  storesWrOk_foldl calls StoresGhost.opened hcalls (StoresWrOk.opened _) rfl rfl

private theorem storeCallPeer_of_mem_fullTrace {peer : AddrVal} {k : IdentityKey}
    {dir : Direction} {r : SessionRecord (List (BitVec 8))}
    {c : StoreCall AddrVal (List (BitVec 8))}
    (h : c ∈ LibsignalSessionApi.fullTrace peer k dir r) :
    StoreCallPeer peer c := by
  simp only [LibsignalSessionApi.fullTrace, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl <;> simp [StoreCallPeer]

theorem messageEncrypt_calls_peer {E : Type} (C : Crypto) (codec : SignalMessageProtoCodec)
    {PQC : Type} (spqr : Spqr (List (BitVec 8)) PQC)
    (ser : AddrVal → AddrVal → Option (List (BitVec 8)))
    (ans : StoreAnswers (List (BitVec 8)) E) (ptext : List (BitVec 8))
    (rem loc : AddrVal) (now : SystemTime) (coins : PQC) :
    ∀ c ∈ (LibsignalSessionApi.messageEncrypt C codec spqr ser ans ptext rem loc now coins).2,
      StoreCallPeer rem c := by
  intro c hc
  obtain ⟨k, r, -, hpref⟩ :=
    LibsignalSessionApi.messageEncrypt_trace_prefix C codec spqr ser ans ptext rem loc now coins
  exact storeCallPeer_of_mem_fullTrace (hpref.subset hc)

theorem messageDecryptSignal_calls_peer {E : Type} (C : Crypto)
    {PQC : Type} (spqr : Spqr (List (BitVec 8)) PQC)
    (ser : AddrVal → AddrVal → Option (List (BitVec 8)))
    (ans : StoreAnswers (List (BitVec 8)) E) (ct : SignalMessage)
    (rem loc : AddrVal) (coins : BitVec 256) :
    ∀ c ∈ (LibsignalSessionApi.messageDecryptSignal C spqr ser ans ct rem loc coins).2,
      StoreCallPeer rem c := by
  intro c hc
  obtain ⟨k, r, -, hpref⟩ :=
    LibsignalSessionApi.messageDecryptSignal_trace_prefix C spqr ser ans ct rem loc coins
  exact storeCallPeer_of_mem_fullTrace (hpref.subset hc)

private theorem commitOk_finish_of_peer {α : Type} {i : Inputs} {P : Party}
    {ans : SlotAns α} {out : α → List (BitVec 8)}
    (hwr : WriteOk i (identityFile (partyAddressName P)) ∧ WriteOk i (sessionFile (partyAddress P)))
    (hg : ∀ g' v, ans = some (some (g', v)) → StoresWrOk (okPeerPath P) g') :
    CommitOk i (MainResult.ofAnswer (finish ans out)) := by
  cases ha : ans with
  | none => trivial
  | some o =>
    cases o with
    | none => intro _ h; cases h
    | some gv =>
      obtain ⟨g', v⟩ := gv
      have hok := hg g' v ha
      intro pw hpw
      have hascii : ∀ w ∈ g'.writes, ∀ b ∈ w.1, b.toNat < 128 :=
        fun w hw => (hok.writes w hw).1
      rw [namedWrites_ascii g'.writes hascii] at hpw
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hpw
      rcases (hok.writes w hw).2 with hp | hp <;> rw [hp]
      · exact hwr.1
      · exact hwr.2

private theorem storesWrOk_encDef {W : PEParams}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {P : Party} {me : AddrVal} {ptext coins : List (BitVec 8)}
    {g' : StoresGhost} {v : CiphertextMessage}
    (h : encDef W Scope F (addrValE P) me ptext coins = some (some (g', v))) :
    StoresWrOk (okPeerPath P) g' := by
  unfold encDef at h
  split at h
  · next m calls heq =>
    injection h with h1
    injection h1 with h2
    obtain ⟨rfl, _⟩ := Prod.mk.inj h2
    exact storesWrOk_cliFinal calls (by
      have hc := messageEncrypt_calls_peer W.C protoSignalCodec (pqxdhSpqrModel W).spqr
        (serializeAddrVals (serviceIdParse uuidTryParse))
        (cliAnswers Scope F (addrValE P) (encKey Scope F (addrValE P)))
        ptext (addrValE P) me unixEpoch coins
      rw [heq] at hc
      exact hc)
  · cases h
  · cases h

private theorem storesWrOk_decSigDef {W : PEParams}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {P : Party} {me : AddrVal} {msg : SignalMessage} {coins : List (BitVec 8)}
    {g' : StoresGhost} {v : List (BitVec 8)}
    (h : decSigDef W Scope F (addrValE P) me msg coins = some (some (g', v))) :
    StoresWrOk (okPeerPath P) g' := by
  unfold decSigDef at h
  split at h
  · next pt calls heq =>
    injection h with h1
    injection h1 with h2
    obtain ⟨rfl, _⟩ := Prod.mk.inj h2
    exact storesWrOk_cliFinal calls (by
      have hc := messageDecryptSignal_calls_peer W.C (pqxdhSpqrModel W).spqr
        (serializeAddrVals (serviceIdParse uuidTryParse))
        (cliAnswers Scope F (addrValE P) (decSigKey W Scope F (addrValE P) me msg coins))
        msg (addrValE P) me (LibsignalTripleRatchetRepr.coinsOf coins)
      rw [heq] at hc
      exact hc)
  · cases h
  · cases h

private theorem storesWrOk_initDef {X : UnreachedPqxdhPrimitives} {W : PEParams}
    {F : FsFiles} {P : Party} {me : AddrVal} {bv : BundleV} {coins : List (BitVec 8)}
    {g' : StoresGhost} {v : Unit}
    (h : initDef X W F (addrValE P) me bv coins = some (some (g', v))) :
    StoresWrOk (okPeerPath P) g' := by
  unfold initDef at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · cases h
    · cases h
    · split at h
      · split at h
        · cases h
        · injection h with h1
          injection h1 with h2
          obtain ⟨rfl, _⟩ := Prod.mk.inj h2
          have h0 := StoresWrOk.opened (okPeerPath P)
          exact { h0 with
            own := by rw [saveUpd_own]; exact h0.own
            peers := DirWrOk.saveUpd h0.peers (okPeerPath_id P)
            sessions := h0.sessions.put (okPeerPath_sess P) _ }
      · cases h

private theorem writeOk_smInputs_peer (g : GhostState (List (BitVec 8))) (cmd : Cmd)
    (coins stdin : List (BitVec 8)) :
    WriteOk (smInputs g cmd coins stdin) (identityFile (partyAddressName g.party.other)) ∧
      WriteOk (smInputs g cmd coins stdin) (sessionFile (partyAddress g.party.other)) := by
  have hw := writeOk_smInputs g cmd coins stdin []
  exact ⟨hw (identityFile (partyAddressName g.party.other), (partyIdentityKey g.party.other).serialize) (by simp [smWrites]),
    hw (sessionFile (partyAddress g.party.other), []) (by simp [smWrites])⟩

private def stWithPeer (W : PEParams) (st : PqParty) : PqParty :=
  { st with
    peerId := some (partyIdentityKey .A)
    session := some (E2E.seedRecordExtras .A,
      (spqrOffSessionParams W.C).initA ⟨0#256, 0#256, 0#256, 0#256, 0#256⟩) }

private theorem mem_encodeDir_stWithPeer (W : PEParams) (st : PqParty) :
    (∃ v₁, (identityFile (partyAddressName st.party.other), v₁) ∈ encodeDir W (stWithPeer W st)) ∧
      (∃ v₂, (sessionFile (partyAddress st.party.other), v₂) ∈ encodeDir W (stWithPeer W st)) := by
  refine ⟨⟨(partyIdentityKey .A).serialize, ?_⟩,
    ⟨encodeRecordUnderExtras (fun _ => E2E.seedRecordExtras .A)
      ((spqrOffSessionParams W.C).initA ⟨0#256, 0#256, 0#256, 0#256, 0#256⟩), ?_⟩⟩ <;>
    simp [encodeDir, stWithPeer]

theorem commitOk_smSend_encDef {S : RunSem} {W : PEParams}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hS : S.encrypt = encDef W Scope)
    (g : GhostState (List (BitVec 8))) (m : List (BitVec 8)) :
    CommitOk (smSendInputs g m) (MainResult.ofAnswer (runAns S (smSendInputs g m))) := by
  rw [runAns_smSend_eq, hS]
  exact commitOk_finish_of_peer (writeOk_smInputs_peer g _ _ _) fun _ _ => storesWrOk_encDef

theorem commitOk_smRecv_decSigDef {S : RunSem} {W : PEParams}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hS : S.decryptSignal = decSigDef W Scope)
    (g : GhostState (List (BitVec 8))) (c : List (BitVec 8)) (rc : BitVec 256) :
    CommitOk (smRecvInputs g c rc) (MainResult.ofAnswer (runAns S (smRecvInputs g c rc))) := by
  rw [runAns_smRecv_eq]
  cases SignalMessage.tryFrom protoSignalCodec c with
  | error _ => intro _ h; cases h
  | ok msg =>
    rw [hS]
    exact commitOk_finish_of_peer (writeOk_smInputs_peer g _ _ _) fun _ _ => storesWrOk_decSigDef

theorem commitOk_pqInit_initDef {S : RunSem} {X : UnreachedPqxdhPrimitives} {W : PEParams}
    (hS : S.initiate = initDef X W)
    (st : PqParty) (b : PreKeyBundleFields) (t : List.Vector (BitVec 8) initiateTapeLen) :
    CommitOk (pqInitInputs W st b t) (MainResult.ofAnswer (runAns S (pqInitInputs W st b t))) := by
  rw [runAns_pqInit_eq]
  cases readBundleV (runFiles (pqInitInputs W st b t)) (bytesOfString bundleDir) 1#8 with
  | none => intro _ h; cases h
  | some bv =>
    rw [hS]
    obtain ⟨⟨v₁, hm₁⟩, ⟨v₂, hm₂⟩⟩ := mem_encodeDir_stWithPeer W st
    have hw := writeOk_pqInitInputs W st (stWithPeer W st) b t
    exact commitOk_finish_of_peer ⟨hw _ hm₁, hw _ hm₂⟩ fun _ _ => storesWrOk_initDef

theorem commitOk_pqSend_encDef {S : RunSem} {W : PEParams}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hS : S.encrypt = encDef W Scope)
    (st : PqParty) (m : List (BitVec 8)) (r : List.Vector (BitVec 8) 64) :
    CommitOk (pqSendInputs W st m r) (MainResult.ofAnswer (runAns S (pqSendInputs W st m r))) := by
  rw [runAns_pqSend_eq, hS]
  obtain ⟨⟨v₁, hm₁⟩, ⟨v₂, hm₂⟩⟩ := mem_encodeDir_stWithPeer W st
  have hw := writeOk_pqSendInputs W st (stWithPeer W st) m r
  exact commitOk_finish_of_peer ⟨hw _ hm₁, hw _ hm₂⟩ fun _ _ => storesWrOk_encDef

theorem commitOk_pqRecvWhisper_decSigDef {S : RunSem} {W : PEParams}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hS : S.decryptSignal = decSigDef W Scope)
    (st : PqParty) (c : List (BitVec 8)) (rc : BitVec 256) :
    CommitOk (pqRecvInputs W st (wireWhisper :: c) rc)
      (MainResult.ofAnswer (runAns S (pqRecvInputs W st (wireWhisper :: c) rc))) := by
  rw [runAns_pqRecvWhisper_eq]
  cases SignalMessage.tryFrom protoSignalCodec c with
  | error _ => intro _ h; cases h
  | ok msg =>
    rw [hS]
    obtain ⟨⟨v₁, hm₁⟩, ⟨v₂, hm₂⟩⟩ := mem_encodeDir_stWithPeer W st
    have hw := writeOk_pqRecvInputs W st (stWithPeer W st) (wireWhisper :: c) rc
    exact commitOk_finish_of_peer ⟨hw _ hm₁, hw _ hm₂⟩ fun _ _ => storesWrOk_decSigDef

theorem commitOk_pqRecvBad (S : RunSem) (W : PEParams) (st : PqParty)
    (c : List (BitVec 8)) (rc : BitVec 256)
    (h2 : c.head? ≠ some wireWhisper) (h3 : c.head? ≠ some wirePrekey) :
    CommitOk (pqRecvInputs W st c rc) (MainResult.ofAnswer (runAns S (pqRecvInputs W st c rc))) := by
  rw [runAns_pqRecvBad S W st c rc h2 h3]
  intro _ h; cases h

end CryptoVerification.SignalSession.Cli.MainHops
