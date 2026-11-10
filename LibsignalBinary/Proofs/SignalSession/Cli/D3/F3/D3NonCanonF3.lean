/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BinaryOomSpec
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.PreKeyGeneralAux
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Domains
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.S0Lemmas.Ok
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Model
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Refine
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Refine.Plumbing
import LibsignalBinary.Proofs.SpecLemmas.FsFold
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Process
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Run
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.RunProofDefs

/-!
# `MainOkValidMatchD3F3` & `MainOkOverD3F3` Specifications and `runAns` Helpers

Side-condition lemmas for `pqRecvInputs`, canonical `pksmParse` / `runAns` equivalence
for arbitrary parsed wire payloads `body`, and the `NeedLocks` + `cliBudgetLimits`
`main`-level specifications `MainOkValidMatchD3F3` and `MainOkOverD3F3`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3NonCanonF3

open Arm64 (FsState GhostName MAX_LFS_FILESIZE Memory normalizePath subroutine_ok)
open Arm64.Obj (MultiPlacement)
open Arm64.Process (bytesOfString initFsState)
open CryptoGames (Party)
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.LibsignalSession (GhostState PublicKey SignalMessage)
open CryptoGames.LibsignalSessionApi (PreKeySignalMessage SessionRecord)
open CryptoVerification.E2E (
  PEParams PreKeyMessageFields RecordExtras UnreachedPqxdhPrimitives partyAddressName wirePrekey
)
open CryptoVerification.E2E.Pqxdh.ResponderWire (PreKeyTryFromArgs)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalTripleRatchetRepr (uuidTryParse)
open CryptoVerification.SignalSession (
  Address ArgvFitsInitialStack CliHooks Cmd Inputs OutcomeMatchesModelExceptPath PqParty
  PqSessionMatches PqxdhPartyInSpecDomain PrintableAsciiArg cliExternsPlaced cliProcessInputs
  coinsFile dirsFold encodeDir fileCapBytes filesFold files_eq_entries initFsState_entries
  loadable_pqRecvInputs observe partyAddress pqRecvInputs pqRecvPrekeyModel pqInputs
  pqxdhExpectedOutcome sessionFile stdinCapBytes stdioPaths
)
open CryptoVerification.SignalSession.Cli (
  CliInputsOk CoinsReadable CommitOk InputsLoadable IsSendOverCap IsStdinOverCap MainResult
  RunAnswer cliInputs
)
open CryptoVerification.SignalSession.Cli.MainHops (CallV cmdTag parseArgs parseArgs_cmd)
open CryptoVerification.SignalSession.Cli.RunCompose (RunSem runAns runFiles)
open CryptoVerification.SignalSession.Cli.RunProofs (decPkDef pkToE? pmOfE)
open CryptoVerification.SignalSession.Cli.RunProofs.DecPkS0 (tryFrom_serialized)
open CryptoVerification.SignalSession.Cli.RunProofs.Pksm (
  decodeProto kyberOk pksmParse pksmParse_bytes
)
open CryptoVerification.SignalSession.Cli.RunRefine (runAns_pqRecvPrekey_eq)
open LibsignalBinary.Heap.Fine (fineCostModel fineHookRustCliAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.D3 (
  D3NoMatchSessionFile decPkDef_eq_pmOfE_of_pkToE?_some
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2 (
  MainOkCliF3OverB2NeedLocksPlacedAt b2MainSpecTightNeedLocksFineAt cliBudgetLimits
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced (
  cliProgExtPlacedAt cliStaticsPlacedAt
)

/-! ## 1. `pqRecvInputs` Side-Condition Helpers -/

private theorem coinsReadable_of_last (i : Inputs) (prefixFiles : List (String × List (BitVec 8)))
    (coins : List (BitVec 8)) (hfiles : i.files = prefixFiles ++ [(coinsFile, coins)])
    (hcap : coins.length ≤ fileCapBytes) :
    CoinsReadable i := by
  unfold CoinsReadable
  rw [files_eq_entries]
  have hne : (normalizePath "coins").isEmpty = false := by decide
  have hns : normalizePath "coins" ∉ stdioPaths.map normalizePath := by decide
  rw [hne, initFsState_entries (cliInputs i) (normalizePath "coins") hns]
  change (filesFold i.files (dirsFold i.dirs {})).entries (normalizePath "coins") ≠ some .dir ∧
    ∀ bs, (filesFold i.files (dirsFold i.dirs {})).entries (normalizePath "coins") = some (.file bs) →
      bs.length ≤ fileCapBytes
  rw [hfiles]
  unfold filesFold
  rw [List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, FsState.setFile, FsState.setEntry, coinsFile]
  refine ⟨by simp, fun bs h => ?_⟩
  simp at h
  subst h
  exact hcap

theorem coinsReadable_pqRecvInputs (W : PEParams) (st : PqParty) (c : List (BitVec 8))
    (rc : BitVec 256) :
    CoinsReadable (pqRecvInputs W st c rc) :=
  coinsReadable_of_last _ (encodeDir W st) (keyToBytes32 rc)
    (by simp [pqRecvInputs, pqInputs])
    (by simp [keyToBytes32, fileCapBytes])

theorem inputsLoadable_pqRecvInputs (W : PEParams) (st : PqParty) (c : List (BitVec 8))
    (rc : BitVec 256) (hst : PqxdhPartyInSpecDomain W st) :
    InputsLoadable (pqRecvInputs W st c rc) := by
  refine ⟨(loadable_pqRecvInputs W st c rc).1, fun f hf =>
    ⟨(loadable_pqRecvInputs W st c rc).2 f hf, ?_⟩⟩
  simp only [pqRecvInputs, pqInputs, List.append_nil, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hf
  rcases hf with h | rfl
  · have hlt := hst.2.1 f h; unfold MAX_LFS_FILESIZE; omega
  · simp [keyToBytes32, MAX_LFS_FILESIZE]

private theorem partyAddress_text_toList (P : Party) :
    (partyAddress P).text.toList = (partyAddressName P).toList ++ ".".toList ++ ['1'] := by
  have ht1 : toString (1 : Nat) = String.singleton (Nat.digitChar 1) := Nat.repr_of_lt (by omega)
  have hd1 : Nat.digitChar 1 = '1' := Nat.digitChar_eq_one.mpr rfl
  simp [partyAddress, Address.text, ht1, hd1, String.toList_append]

private theorem partyAddress_text_printable (P : Party) :
    PrintableAsciiArg (partyAddress P).text := by
  have ht1 : toString (1 : Nat) = String.singleton (Nat.digitChar 1) := Nat.repr_of_lt (by omega)
  refine ⟨?_, ?_⟩
  · intro h
    have hl := congrArg String.utf8ByteSize h
    simp [partyAddress, Address.text, ht1, String.utf8ByteSize_append] at hl
  · intro c hc
    rw [partyAddress_text_toList] at hc
    cases P <;> revert c hc <;> decide

private theorem partyAddress_text_length (P : Party) :
    (partyAddress P).text.length = 38 := by
  rw [← String.length_toList, partyAddress_text_toList]
  cases P <;> decide

theorem cliInputsOk_pqRecvInputs (W : PEParams) (st : PqParty) (c : List (BitVec 8))
    (rc : BitVec 256) :
    CliInputsOk (pqRecvInputs W st c rc) := by
  refine ⟨?_, ?_⟩
  · intro a ha
    simp only [pqRecvInputs, pqInputs, Cmd.argv, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · unfold PrintableAsciiArg; decide
    · exact partyAddress_text_printable st.party.other
  · unfold ArgvFitsInitialStack pqRecvInputs pqInputs Cmd.argv
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      partyAddress_text_length]
    decide

theorem not_isStdinOverCap_of_stdin_le {i : Inputs} (h : i.stdin.length ≤ stdinCapBytes) :
    ¬ IsStdinOverCap i :=
  fun ⟨_, hgt⟩ => Nat.not_lt.mpr h hgt

theorem not_isSendOverCap_pqRecvInputs (W : PEParams) (st : PqParty) (c : List (BitVec 8))
    (rc : BitVec 256) :
    ¬ IsSendOverCap (pqRecvInputs W st c rc) := by
  rintro ⟨⟨peer, hp⟩, -⟩
  obtain ⟨v, hv, htag⟩ := parseArgs_cmd (.recv (partyAddress st.party.other)) rfl
  change parseArgs uuidTryParse
    ((Cmd.recv (partyAddress st.party.other)).argv.map bytesOfString) = some (.send peer) at hp
  rw [hp] at hv
  injection hv with heq
  subst heq
  simp [CallV.tag, cmdTag] at htag

theorem isStdinOverCap_pqRecvInputs (W : PEParams) (st : PqParty) (c : List (BitVec 8))
    (rc : BitVec 256) (h : stdinCapBytes < c.length) :
    IsStdinOverCap (pqRecvInputs W st c rc) := by
  refine ⟨?_, h⟩
  obtain ⟨v, hv, htag⟩ := parseArgs_cmd (.recv (partyAddress st.party.other)) rfl
  exact ⟨v, hv, by rw [htag]; simp [cmdTag]⟩

/-! ## 2. Pure `pksmParse` & `runAns` Canonicalization Helpers -/

private theorem tryFrom_inner_of_pksmParse_pkToE {body : List (BitVec 8)} {pm : PreKeySignalMessage}
    {m : PreKeyMessageFields} (hparse : pksmParse body = some pm) (hpk : pkToE? pm = some m) :
    SignalMessage.tryFrom protoSignalCodec m.inner = .ok pm.message := by
  have hm_inner : m.inner = pm.message.serialized := by
    unfold pkToE? at hpk
    split at hpk
    · cases hpk
    · split at hpk
      · cases hpk
      · split at hpk
        · cases hpk
        · injection hpk with hm
          exact (congrArg PreKeyMessageFields.inner hm).symm
  cases body with
  | nil => cases hparse
  | cons vb rest =>
    unfold pksmParse at hparse
    dsimp only at hparse
    split at hparse
    · cases hparse
    · rcases hdec : decodeProto rest with _ | mp
      · simp [hdec] at hparse
      rw [hdec] at hparse
      rcases hbk : mp.baseKey with _ | bk
      · simp [hbk] at hparse
      rcases hik : mp.identityKey with _ | ik
      · simp [hbk, hik] at hparse
      rcases hmsg : mp.message with _ | rawMsg
      · simp [hbk, hik, hmsg] at hparse
      rcases hsid : mp.signedPreKeyId with _ | sid
      · simp [hbk, hik, hmsg, hsid] at hparse
      simp only [hbk, hik, hmsg, hsid] at hparse
      cases hkyb : kyberOk (vb >>> 4) mp
      · simp [hkyb] at hparse
      simp only [hkyb, ↓reduceIte] at hparse
      rcases h1 : PublicKey.deserialize bk with _ | baseKey
      · simp [h1] at hparse
      rcases h2 : PublicKey.deserialize ik with _ | idKey
      · simp [h1, h2] at hparse
      rcases h3 : SignalMessage.tryFrom protoSignalCodec rawMsg with _ | inner
      · simp [h1, h2, h3] at hparse
      simp only [h1, h2, h3, Option.some.injEq] at hparse
      subst hparse
      have hser : inner.serialized = rawMsg := tryFrom_serialized h3
      dsimp only at hm_inner ⊢
      rw [hm_inner, hser]
      exact h3

/-- Canonical `pksmParse m.bytes` evaluates to `some (pmOfE m pm.message)` whenever
`pksmParse body = some pm` and `pkToE? pm = some m` with `m.inner.length + 2048 < 2 ^ 32`. -/
theorem pksmParse_bytes_of_parse_pkToE {body : List (BitVec 8)} {pm : PreKeySignalMessage}
    {m : PreKeyMessageFields} (hparse : pksmParse body = some pm) (hpk : pkToE? pm = some m)
    (hm : m.inner.length + 2048 < 2 ^ 32) :
    pksmParse m.bytes = some (pmOfE m pm.message) := by
  have hi := tryFrom_inner_of_pksmParse_pkToE hparse hpk
  let x : PreKeyTryFromArgs :=
    { ptr := 0, sret := 0, regId := m.regId, opkId := m.opkId, spkId := m.spkId,
      kpkId := m.kpkId, kyberCt := m.kyberCt, baseKey := m.baseKey, idPub := m.idPub,
      inner := m.inner }
  have h := pksmParse_bytes x hm
  change pksmParse m.bytes =
    (match SignalMessage.tryFrom protoSignalCodec m.inner with
     | .ok i => some (pmOfE m i)
     | .error _ => none) at h
  rw [h, hi]

/-- `runAns S` on `pqRecvInputs WP st (wirePrekey :: body) rc` equals `runAns S` on canonical
`pqRecvInputs WP st (wirePrekey :: m.bytes) rc` whenever `S.pksmParse = pksmParse`,
`S.decryptPrekey = decPkDef X WP Scope`, `pksmParse body = some pm`, `pkToE? pm = some m`,
and `m.inner.length + 2048 < 2 ^ 32`. -/
theorem runAns_pqRecvPrekey_eq_canonical (S : RunSem) (X : UnreachedPqxdhPrimitives)
    (WP : PEParams) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hS_pksm : S.pksmParse = pksmParse) (hS_decPk : S.decryptPrekey = decPkDef X WP Scope)
    (st : PqParty) (body : List (BitVec 8)) (pm : PreKeySignalMessage) (m : PreKeyMessageFields)
    (rc : BitVec 256) (hparse : pksmParse body = some pm) (hpk : pkToE? pm = some m)
    (hm : m.inner.length + 2048 < 2 ^ 32) :
    runAns S (pqRecvInputs WP st (wirePrekey :: body) rc) =
      runAns S (pqRecvInputs WP st (wirePrekey :: m.bytes) rc) := by
  have hcanon := pksmParse_bytes_of_parse_pkToE hparse hpk hm
  have hfiles_eq :
      (initFsState (cliInputs (pqRecvInputs WP st (wirePrekey :: body) rc))).files =
      (initFsState (cliInputs (pqRecvInputs WP st (wirePrekey :: m.bytes) rc))).files := rfl
  rw [runAns_pqRecvPrekey_eq, runAns_pqRecvPrekey_eq, hS_pksm, hparse, hcanon, hS_decPk]
  dsimp only [runFiles]
  rw [decPkDef_eq_pmOfE_of_pkToE?_some hpk, hfiles_eq]

/-! ## 3. `NeedLocks` + `cliBudgetLimits` `main` Specifications -/

/-- `NeedLocks` + `cliBudgetLimits` `main`-level specification for empty-or-matching
session pre-key `recv` on arbitrary valid wire payloads `body`. -/
def MainOkValidMatchD3F3
    (mpl mmpl : MultiPlacement) (CodeOk : Memory → Prop)
    (libcAddr brkStart : BitVec 64) (stk : Nat) : Prop :=
  mpl.base 547 ≠ 0#64 →
  ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks),
    let WP : PEParams := ⟨W.C, W.Q⟩
    ∃ Run : Inputs → RunAnswer → Prop,
      (∀ (γ : GhostName) (tp : BitVec 64),
        subroutine_ok (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) (mpl.base 617)
          (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp brkStart)
            cliBudgetLimits fineCostModel.init stk (cliStaticsPlacedAt mpl)
            Run cliProcessInputs)) ∧
      ∀ (st : PqParty), PqxdhPartyInSpecDomain WP st →
        ∀ (body : List (BitVec 8)) (pm : PreKeySignalMessage) (m : PreKeyMessageFields)
          (rc : BitVec 256),
          body.length < 2 ^ 32 →
          pksmParse body = some pm →
          pkToE? pm = some m →
          m.inner.length + 2048 < 2 ^ 32 →
          (∀ x g, st.session = some (x, g) → PqSessionMatches x g m) →
          let inp := pqRecvInputs WP st (wirePrekey :: body) rc
          ∃ a, Run inp a ∧
            observe inp.files a = pqxdhExpectedOutcome WP inp (pqRecvPrekeyModel X WP st m rc) ∧
            CommitOk inp (MainResult.ofAnswer a)

/-- `NeedLocks` + `cliBudgetLimits` `main`-level specification for non-matching session
pre-key `recv` on arbitrary parsed wire payloads `body` (`validOver`) and canonical `m.bytes`
(`canonicalNoMatch`), establishing `OutcomeMatchesModelExceptPath` outside the peer session
file and `D3NoMatchSessionFile` on the peer session file. -/
def MainOkOverD3F3
    (mpl mmpl : MultiPlacement) (CodeOk : Memory → Prop)
    (libcAddr brkStart : BitVec 64) (stk : Nat) : Prop :=
  mpl.base 547 ≠ 0#64 →
  ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks),
    let WP : PEParams := ⟨W.C, W.Q⟩
    ∃ Run : Inputs → RunAnswer → Prop,
      (∀ (γ : GhostName) (tp : BitVec 64),
        subroutine_ok (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) (mpl.base 617)
          (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp brkStart)
            cliBudgetLimits fineCostModel.init stk (cliStaticsPlacedAt mpl)
            Run cliProcessInputs)) ∧
      (∀ (st : PqParty), PqxdhPartyInSpecDomain WP st →
        ∀ (x : RecordExtras) (g : GhostState (List (BitVec 8))), st.session = some (x, g) →
        ∀ (body : List (BitVec 8)) (pm : PreKeySignalMessage) (m : PreKeyMessageFields)
          (rc : BitVec 256),
          body.length < 2 ^ 32 →
          pksmParse body = some pm →
          pkToE? pm = some m →
          m.inner.length + 2048 < 2 ^ 32 →
          ¬ PqSessionMatches x g m →
          let inp := pqRecvInputs WP st (wirePrekey :: body) rc
          ∃ a, Run inp a ∧
            (OutcomeMatchesModelExceptPath WP inp (sessionFile (partyAddress st.party.other))
               (pqRecvPrekeyModel X WP { st with session := none } m rc)
               (observe inp.files a) ∧
             D3NoMatchSessionFile X WP st x g m rc (observe inp.files a)) ∧
            CommitOk inp (MainResult.ofAnswer a)) ∧
      (∀ (st : PqParty), PqxdhPartyInSpecDomain WP st →
        ∀ (x : RecordExtras) (g : GhostState (List (BitVec 8))), st.session = some (x, g) →
        ∀ (m : PreKeyMessageFields) (rc : BitVec 256),
          m.inner.length + 2048 < 2 ^ 32 →
          ¬ PqSessionMatches x g m →
          let inp := pqRecvInputs WP st (wirePrekey :: m.bytes) rc
          ∃ a, Run inp a ∧
            (OutcomeMatchesModelExceptPath WP inp (sessionFile (partyAddress st.party.other))
               (pqRecvPrekeyModel X WP { st with session := none } m rc)
               (observe inp.files a) ∧
             D3NoMatchSessionFile X WP st x g m rc (observe inp.files a)) ∧
            CommitOk inp (MainResult.ofAnswer a))

/-- Clause-split arbitrary-`body` half of `MainOkOverD3F3` at a fixed `RunOf`. -/
def MainOkValidOverBodyD3F3
    (mpl mmpl : MultiPlacement) (CodeOk : Memory → Prop)
    (libcAddr brkStart : BitVec 64) (stk : Nat)
    (RunOf : UnreachedPqxdhPrimitives → CliHooks → Inputs → RunAnswer → Prop) : Prop :=
  mpl.base 547 ≠ 0#64 →
  ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks),
    let WP : PEParams := ⟨W.C, W.Q⟩
    let Run := RunOf X W
    (∀ (γ : GhostName) (tp : BitVec 64),
      subroutine_ok (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) (mpl.base 617)
        (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk
          (fineHookRustCliAllocBudget γ mmpl tp brkStart)
          cliBudgetLimits fineCostModel.init stk (cliStaticsPlacedAt mpl)
          Run cliProcessInputs)) ∧
    ∀ (st : PqParty), PqxdhPartyInSpecDomain WP st →
      ∀ (x : RecordExtras) (g : GhostState (List (BitVec 8))), st.session = some (x, g) →
      ∀ (body : List (BitVec 8)) (pm : PreKeySignalMessage) (m : PreKeyMessageFields)
        (rc : BitVec 256),
        body.length < 2 ^ 32 →
        pksmParse body = some pm →
        pkToE? pm = some m →
        m.inner.length + 2048 < 2 ^ 32 →
        ¬ PqSessionMatches x g m →
        let inp := pqRecvInputs WP st (wirePrekey :: body) rc
        ∃ a, Run inp a ∧
          (OutcomeMatchesModelExceptPath WP inp (sessionFile (partyAddress st.party.other))
             (pqRecvPrekeyModel X WP { st with session := none } m rc)
             (observe inp.files a) ∧
           D3NoMatchSessionFile X WP st x g m rc (observe inp.files a)) ∧
          CommitOk inp (MainResult.ofAnswer a)

/-- Clause-split canonical-`m.bytes` half of `MainOkOverD3F3` at a fixed `RunOf`. -/
def MainOkCanonNoMatchD3F3
    (mpl : MultiPlacement)
    (RunOf : UnreachedPqxdhPrimitives → CliHooks → Inputs → RunAnswer → Prop) : Prop :=
  mpl.base 547 ≠ 0#64 →
  ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks),
    let WP : PEParams := ⟨W.C, W.Q⟩
    let Run := RunOf X W
    ∀ (st : PqParty), PqxdhPartyInSpecDomain WP st →
      ∀ (x : RecordExtras) (g : GhostState (List (BitVec 8))), st.session = some (x, g) →
      ∀ (m : PreKeyMessageFields) (rc : BitVec 256),
        m.inner.length + 2048 < 2 ^ 32 →
        ¬ PqSessionMatches x g m →
        let inp := pqRecvInputs WP st (wirePrekey :: m.bytes) rc
        ∃ a, Run inp a ∧
          (OutcomeMatchesModelExceptPath WP inp (sessionFile (partyAddress st.party.other))
             (pqRecvPrekeyModel X WP { st with session := none } m rc)
             (observe inp.files a) ∧
           D3NoMatchSessionFile X WP st x g m rc (observe inp.files a)) ∧
          CommitOk inp (MainResult.ofAnswer a)

/-- Combines `MainOkValidOverBodyD3F3` and `MainOkCanonNoMatchD3F3` into `MainOkOverD3F3`. -/
theorem mainOkOverD3F3_of_clauses
    {mpl mmpl : MultiPlacement} {CodeOk : Memory → Prop}
    {libcAddr brkStart : BitVec 64} {stk : Nat}
    {RunOf : UnreachedPqxdhPrimitives → CliHooks → Inputs → RunAnswer → Prop}
    (hbody : MainOkValidOverBodyD3F3 mpl mmpl CodeOk libcAddr brkStart stk RunOf)
    (hcanon : MainOkCanonNoMatchD3F3 mpl RunOf) :
    MainOkOverD3F3 mpl mmpl CodeOk libcAddr brkStart stk := by
  intro hDropNz X W
  obtain ⟨hmain, hbodyCl⟩ := hbody hDropNz X W
  exact ⟨RunOf X W, hmain, hbodyCl, hcanon hDropNz X W⟩

abbrev MainOkValidOverD3F3 := MainOkOverD3F3

/-- Projects `MainOkOverD3F3` directly onto `L4B.CliStrictPlaced2.MainOkCliF3OverB2NeedLocksPlacedAt`
by dropping the `D3NoMatchSessionFile` conjunct on canonical `m.bytes` inputs. -/
theorem mainOkCliF3Over_of_mainOkOverD3F3
    {mpl mmpl : MultiPlacement} {CodeOk : Memory → Prop}
    {libcAddr brkStart : BitVec 64} {stk : Nat}
    (hoverD3 : MainOkOverD3F3 mpl mmpl CodeOk libcAddr brkStart stk) :
    MainOkCliF3OverB2NeedLocksPlacedAt mpl mmpl CodeOk libcAddr brkStart stk := by
  intro hDropNz X W
  obtain ⟨Run, hmain, _, hcanon⟩ := hoverD3 hDropNz X W
  refine ⟨Run, hmain, fun st hst x g hsess m rc hinner hnomatch => ?_⟩
  obtain ⟨a, hrun, ⟨hobs, _⟩, hcommit⟩ := hcanon st hst x g hsess m rc hinner hnomatch
  exact ⟨a, hrun, hobs, hcommit⟩

end LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3NonCanonF3
