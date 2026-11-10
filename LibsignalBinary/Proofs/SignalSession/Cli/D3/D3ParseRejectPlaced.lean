/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.GamePaths
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Domains
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFromPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Refine.Bounds
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.EncOk
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ScopeIn
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.Oblig.EncSessionInj
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.S0Proofs
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSessionApiFacts
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Run
import Init.Data.Repr
import Init.Data.String.Basic
import Init.Data.String.Defs
import Init.Data.ToString.Basic

/-!
# Whole-Process Pre-Key `recv` Combinators & Unparseable Payload Rejection

Generic `OutcomeOrExcusedAbort` combinators for `pqRecvInputs` from `mainSpecTightPlaced`
contracts, plus whole-process rejection when `Pksm.pksmParse body = none`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.D3

open Arm64 Arm64.Process ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunRefine
open CryptoVerification.SignalSession.Cli.RunProofs

/-! ## 1. Pure PQXDH Domain Helpers & `RunHsOk` on `pqRecvInputs` -/

theorem encodeInjOn_scopeIn_placed : Slots.EncodeInjOn Slots.scopeIn :=
  fun r₁ r₂ h₁ h₂ henc =>
    Slots.encodeInjOn_deserializeScopeP_Q r₁ r₂
      (Slots.scopeKit_of_scopeIn h₁) (Slots.scopeKit_of_scopeIn h₂) henc

theorem ratchetScopeCoversPq_scopeIn_placed (W : PEParams) :
    ∀ st x g, PqxdhPartyInSpecDomain W st → st.session = some (x, g) →
      Slots.scopeIn (E2E.Record.toRecord (E2E.RecordX.extrasOf fun _ => x) g) := by
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
  · intro s hs'; injection hs' with hs'; subst hs'
    refine ⟨hseeds₀, Nat.lt_of_le_of_lt hrc₀ (by decide), ?_⟩
    intro k hk'; unfold E2E.RecordX.sessionOfX at hk'; dsimp only at hk'
    split at hk'
    · rw [hky k hk']; decide
    · cases hk'
  · intro s hs'; injection hs' with hs'; subst hs'; exact ⟨hval, hpq31⟩
  · intro s hs'; injection hs' with hs'; subst hs'
    refine ⟨hrepr₀.1, hrepr₀.2, E2E.RecordX.sessionOfX_wf (fun _ => x) g, ?_⟩
    show x.aliceBaseKey.length < 2 ^ 32; rw [habk]; decide
  · refine ⟨hrc₀, ?_, ?_, Or.inr habk⟩
    · intro p hp; unfold E2E.RecordX.sessionOfX at hp; dsimp only at hp
      split at hp
      · injection hp with hp'; subst hp'; exact hts
      · cases hp
    · intro k hk'; unfold E2E.RecordX.sessionOfX at hk'; dsimp only at hk'
      split at hk'
      · exact hky k hk'
      · cases hk'

theorem runFilesOk_pqRecv_cli_placed {S : RunSem}
    (hS : S.filesOk = Slots.filesOk₀ Slots.scopeIn (fun _ => True))
    (W : PEParams) (st : PqParty) (c : List (BitVec 8)) (rc : BitVec 256)
    (hwf : PqxdhPartyInSpecDomain W st) :
    RunFilesOk S (pqRecvInputs W st c rc) :=
  Slots.runFilesOk_of_peer (.recv (partyAddress st.party.other)) rfl rfl
    (ownAddr_pqRecv W st c rc)
    (hS ▸ ⟨Slots.filesOkPeer_pqRecv W st c rc
      (fun x g hs => ratchetScopeCoversPq_scopeIn_placed W st x g hwf hs)
      (Slots.pqSessBytes_le_fileCapBytes hwf),
      Slots.distinctSid_party st.party, trivial⟩)

theorem inputsLoadable_pqRecvInputs_placed (W : PEParams) (st : PqParty) (c : List (BitVec 8))
    (rc : BitVec 256) (hst : PqxdhPartyInSpecDomain W st) :
    Cli.InputsLoadable (pqRecvInputs W st c rc) := by
  refine ⟨(loadable_pqRecvInputs W st c rc).1, fun f hf =>
    ⟨(loadable_pqRecvInputs W st c rc).2 f hf, ?_⟩⟩
  simp only [pqRecvInputs, pqInputs, List.append_nil, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hf
  rcases hf with h | rfl
  · have hlt := hst.2.1 f h; unfold MAX_LFS_FILESIZE; omega
  · simp [HMAC.keyToBytes32, MAX_LFS_FILESIZE]

theorem coinsReadable_pqRecvInputs_placed (W : PEParams) (st : PqParty) (c : List (BitVec 8))
    (rc : BitVec 256) :
    Cli.CoinsReadable (pqRecvInputs W st c rc) :=
  Cli.coinsReadable_pqInputs W st _ _ _ _ (Or.inl rfl)

private theorem partyAddress_text_toList_placed (P : Party) :
    (partyAddress P).text.toList = (partyAddressName P).toList ++ ".".toList ++ ['1'] := by
  have ht1 : toString (1 : Nat) = String.singleton (Nat.digitChar 1) := Nat.repr_of_lt (by omega)
  have hd1 : Nat.digitChar 1 = '1' := Nat.digitChar_eq_one.mpr rfl
  simp [partyAddress, Address.text, ht1, hd1, String.toList_append]

private theorem partyAddress_text_printable_placed (P : Party) :
    PrintableAsciiArg (partyAddress P).text := by
  have ht1 : toString (1 : Nat) = String.singleton (Nat.digitChar 1) := Nat.repr_of_lt (by omega)
  refine ⟨?_, ?_⟩
  · intro h
    have hl := congrArg String.utf8ByteSize h
    simp [partyAddress, Address.text, ht1, String.utf8ByteSize_append] at hl
  · intro ch hch
    rw [partyAddress_text_toList_placed] at hch
    cases P <;> revert ch hch <;> decide

private theorem partyAddress_text_length_placed (P : Party) :
    (partyAddress P).text.length = 38 := by
  rw [← String.length_toList, partyAddress_text_toList_placed]
  cases P <;> decide

theorem cliInputsOk_pqRecvInputs_placed (W : PEParams) (st : PqParty) (c : List (BitVec 8))
    (rc : BitVec 256) :
    Cli.CliInputsOk (pqRecvInputs W st c rc) := by
  refine ⟨?_, ?_⟩
  · intro a ha
    simp only [pqRecvInputs, pqInputs, Cmd.argv, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · unfold PrintableAsciiArg; decide
    · exact partyAddress_text_printable_placed st.party.other
  · unfold ArgvFitsInitialStack pqRecvInputs pqInputs Cmd.argv
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      partyAddress_text_length_placed]
    decide

def defaultModelExtras_placed : UnreachedPqxdhPrimitives where
  sigPkGen _ := []
  sigSign _ _ _ := []
  scalarMul _ _ := []
  scalarAdd _ _ := []
  kemKeyGen _ := ([], [])
  pow8 _ := []
  isValidDhTriple _ _ _ := false

noncomputable def cliRunSem_placed (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (decPk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → List (BitVec 8) →
      SlotAns (List (BitVec 8)))
    (decPkOk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → Prop)
    (pksmParse : List (BitVec 8) → Option PreKeySignalMessage) : RunSem where
  encrypt := fun _ _ _ _ _ => some none
  decryptSignal := fun _ _ _ _ _ => some none
  initiate := initDef X ⟨W.C, W.Q⟩
  decryptPrekey := decPk
  pksmParse := pksmParse
  filesOk := Slots.filesOk₀ Slots.scopeIn (fun _ => True)
  encOk := Slots.encOk₀ Slots.scopeIn
  initOk := InitOk₀ ⟨W.C, W.Q⟩
  decPkOk := decPkOk

/-- When `S.decPkOk` holds on `runFiles (pqRecvInputs WP st (wirePrekey :: body) rc)` for all
`pm`, `RunHsOk S (pqRecvInputs WP st (wirePrekey :: body) rc)` holds for any wire payload `body`. -/
theorem runHsOk_pqRecvPrekey_of_decPkOk_any {S : RunSem}
    (WP : PEParams) (st : PqParty) (body : List (BitVec 8)) (rc : BitVec 256)
    (hdec : ∀ pm, S.decPkOk (runFiles (pqRecvInputs WP st (wirePrekey :: body) rc))
      (addrValE st.party.other) (addrValE st.party) pm) :
    RunHsOk S (pqRecvInputs WP st (wirePrekey :: body) rc) := by
  have ha : (pqRecvInputs WP st (wirePrekey :: body) rc).argv =
      (Cmd.recv (partyAddress st.party.other)).argv := rfl
  have hin : (pqRecvInputs WP st (wirePrekey :: body) rc).stdin = wirePrekey :: body := rfl
  refine ⟨fun peer dir _ _ h _ _ => ?_, fun peer ownB meV rest pm hparse hown hme hstdin _ => ?_⟩
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
    exact hdec pm

/-! ## 2. Unparseable Pre-Key Wire Payload Rejection (`Pksm.pksmParse body = none`) -/

/-- `RunSem` bundle for `Pksm.pksmParse body = none` with vacuous `decPkOk`. -/
noncomputable abbrev cliRunSemParseNone (W : CliHooks) : RunSem :=
  cliRunSem_placed defaultModelExtras_placed W (fun _ _ _ _ _ => some none) (fun _ _ _ _ => False) Pksm.pksmParse

end LibsignalBinary.Proofs.SignalSession.Cli.D3
