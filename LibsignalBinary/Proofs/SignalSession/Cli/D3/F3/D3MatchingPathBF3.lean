/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BinaryOomSpec
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3ParseRejectF3
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.CommitOk
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.E2E.RecordX.BridgeCommon
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Domains
import LibsignalBinary.Proofs.SignalSession.Cli.Main.IoHooks
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.S0Lemmas.AgreeCoins
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.S0Lemmas.AgreeCommit
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.S0Lemmas.AgreeStore
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.S0Lemmas.Ok
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.S0Lemmas.Agree
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Refine.Bounds
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Refine.Plumbing
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.EncOk
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.LoadRec
import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSessionApiFacts
import ProofLib.ProgramReflection

/-!
# Two-Placement Matching-Session Path-B `RunSem` & Whole-Process Proofs

Pure `DecPkOkPathB` domain agreement, `cliRunSemPathB`, `MainOkPathBD3F3`, and
two-placement `(mpl, mmpl)` whole-process evaluation theorems (`d3_matchingPathB_strict_of_f3`,
`d3_matchingPathB_f3`) for matching-session Path-B pre-key `recv`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3MatchingPathBF3

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.ProgramReflection
open CryptoGames (Party)
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.LibsignalSession (GhostState SessionState)
open CryptoGames.LibsignalSessionApi (PreKeySignalMessage Session SessionRecord)
open CryptoVerification.E2E (
  PEParams RecordExtras UnreachedPqxdhPrimitives encodeRecordUnderExtras pqxdhSessionParams
  pqxdhSpqrSession wirePrekey
)
open CryptoVerification.E2E.Record (toRecord)
open CryptoVerification.E2E.RecordX (extrasOf toSessionExtras)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal)
open CryptoVerification.SignalSession (
  CliHooks CliReachesOOMPlaced Cmd Outcome OutcomeOrExcusedAbort PqParty
  PqxdhPartyInSpecDomain cliExternsPlaced cliProcessInputs filesOf observe partyAddress
  pqRecvInputs pqxdhExpectedOutcome stdinCapBytes
)
open CryptoVerification.SignalSession.Cli (
  CommitOk IdGhost MainResult StoresGhost baseKeysName utf8
)
open CryptoVerification.SignalSession.Cli.MainHops (cliIo domainArgv_pqRecv)
open CryptoVerification.SignalSession.Cli.RunCompose (
  RunHsOk RunSem finish runAns runFiles runRel
)
open CryptoVerification.SignalSession.Cli.RunProofs (
  PreKeyFilesWf ScopeCoversPq SessMatchesPm
  commitOk_pqRecvPrekey_decPkDef decPkDef initParty pkRecvCoins
)
open CryptoVerification.SignalSession.Cli.RunProofs.DecPkS0 (
  baseKeysLt_pqRecv encodeRecord_cleared_eq_encodeRecordX filesOf_commit_master find?_self_double
  idPeer_pqRecv keyPairLt_pqRecv kyberLastResortWf_pqRecv kyberOneTimeWf_pqRecv loadRec_pqRecv_eq
  namedWrites_of_dirs oneTimeWf_pqRecv pkRecvCoins_keyToBytes32 recvBucket_identityFile
  recvBucket_sessionFile signedWf_pqRecv
)
open CryptoVerification.SignalSession.Cli.RunProofs.InitS0 (initParty_eq)
open CryptoVerification.SignalSession.Cli.RunProofs.Pksm (pksmParse)
open CryptoVerification.SignalSession.Cli.RunRefine (
  addrParse_textBytes addrValE ownAddr_pqRecv parseArgs_recv runAns_pqRecvPrekey_eq runBounds_pqRecv
)
open CryptoVerification.SignalSession.Cli.Slots (EncodeInjOn loadRec runEncOk_pqRecv scopeIn)
open CryptoVerification.SignalSession.Placed (cliRunPlacedSig)
open LibsignalBinary.Heap.Fine (fineCostModel fineHookRustCliAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.D3 (d3PqRecvMatchingModel d3PqSessionOf)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3ParseRejectF3 (
  cliRunSemF3 defaultExtrasF3 encodeInjOn_scopeIn pqD3ScopedRun pqRecv_strict_obs_of_f3B2NeedLocks
  ratchetScopeCoversPq_scopeIn runFilesOk_pqRecv_cli_f3
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2 (
  CliElfF3B2NeedLocksAssumptions b2MainSpecTightNeedLocksFineAt cliBudgetLimits
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced (
  cliProgExtPlacedAt cliStaticsPlacedAt
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.PlacedOomRecovery2 (outcomeOrExcusedAbort_of_eq)

/-! ## 1. Pure `DecPkOkPathB` & `d3PqRecvMatchingModel` Agreement -/

/-- File-domain precondition for the matching-session Path-B branch of `decrypt_prekey`. -/
structure DecPkOkPathB (W : PEParams) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (F : FsFiles) (peer me : AddrVal) (pm : PreKeySignalMessage) : Prop where
  party : ∃ P : Party, peer = addrValE P.other ∧ me = addrValE P
  loadedMatch : ∃ s : Session (List (BitVec 8)),
    loadRec Scope F peer = .ok (some ⟨some s⟩) ∧ SessMatchesPm s pm
  keyPairLt : ∀ bs,
    StoresGhost.opened.identity.own.get cliIo.rd F (utf8 "identity-key-pair") = .ok bs →
    bs.length < 2 ^ 32
  preKeysWf : PreKeyFilesWf W F
  baseKeysLt : ∀ i bs,
    StoresGhost.opened.kyber.lastResort.get cliIo.rd F (baseKeysName i) = .ok bs →
    bs.length < 2 ^ 32

theorem decPkOkPathB_pqRecv (W : PEParams)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hinj : EncodeInjOn Scope) (hcov : ScopeCoversPq W Scope)
    (st : PqParty) (x : RecordExtras) (g : GhostState (List (BitVec 8)))
    (body : List (BitVec 8)) (pm : PreKeySignalMessage) (rc : BitVec 256)
    (hwf : PqxdhPartyInSpecDomain W st) (hsess : st.session = some (x, g))
    (hmatch : SessMatchesPm (d3PqSessionOf x g) pm) :
    DecPkOkPathB W Scope (runFiles (pqRecvInputs W st (wirePrekey :: body) rc))
      (addrValE st.party.other) (addrValE st.party) pm := by
  refine ⟨⟨st.party, rfl, rfl⟩, ⟨d3PqSessionOf x g, ?_, hmatch⟩,
    keyPairLt_pqRecv W st _ rc hwf,
    ⟨signedWf_pqRecv W st _ rc, oneTimeWf_pqRecv W st _ rc,
      kyberOneTimeWf_pqRecv W st _ rc, kyberLastResortWf_pqRecv W st _ rc⟩,
    baseKeysLt_pqRecv W st _ rc hwf⟩
  rw [loadRec_pqRecv_eq hinj hcov st (wirePrekey :: body) rc hwf, hsess]; rfl

theorem runHsOk_pqRecv_matchingPathB (S : RunSem) (W : PEParams)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hdec : ∀ F peer me pm, DecPkOkPathB W Scope F peer me pm → S.decPkOk F peer me pm)
    (hpksm : S.pksmParse = pksmParse)
    (hinj : EncodeInjOn Scope) (hcov : ScopeCoversPq W Scope)
    (st : PqParty) (x : RecordExtras) (g : GhostState (List (BitVec 8)))
    (body : List (BitVec 8)) (pm : PreKeySignalMessage) (rc : BitVec 256)
    (hwf : PqxdhPartyInSpecDomain W st) (hsess : st.session = some (x, g))
    (hparse : pksmParse body = some pm)
    (hmatch : SessMatchesPm (d3PqSessionOf x g) pm) :
    RunHsOk S (pqRecvInputs W st (wirePrekey :: body) rc) := by
  have ha : (pqRecvInputs W st (wirePrekey :: body) rc).argv =
      (Cmd.recv (partyAddress st.party.other)).argv := rfl
  refine ⟨?_, ?_⟩
  · intro _ _ _ _ hp; rw [ha, parseArgs_recv] at hp; cases hp
  · intro _ _ _ rest pm' hp hown had hin hparse'
    rw [ha, parseArgs_recv] at hp; cases hp
    rw [ownAddr_pqRecv] at hown; cases hown
    rw [addrParse_textBytes] at had; cases had
    have hstdin : (pqRecvInputs W st (wirePrekey :: body) rc).stdin = 3#8 :: body := rfl
    rw [hstdin] at hin; injection hin with _ hrest; subst hrest
    rw [hpksm, hparse] at hparse'; injection hparse' with hpm; subst hpm
    exact hdec _ _ _ _ (decPkOkPathB_pqRecv W Scope hinj hcov st x g body pm rc hwf hsess hmatch)

theorem observe_runAns_pqRecv_matchingPathB (S : RunSem) (X : UnreachedPqxdhPrimitives)
    (W : PEParams) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hS : S.decryptPrekey = decPkDef X W Scope) (hpksm : S.pksmParse = pksmParse)
    (hinj : EncodeInjOn Scope) (hcov : ScopeCoversPq W Scope)
    (st : PqParty) (x : RecordExtras) (g : GhostState (List (BitVec 8)))
    (body : List (BitVec 8)) (pm : PreKeySignalMessage) (rc : BitVec 256)
    (hwf : PqxdhPartyInSpecDomain W st) (hsess : st.session = some (x, g))
    (hparse : pksmParse body = some pm) (hmatch : SessMatchesPm (d3PqSessionOf x g) pm) :
    observe (pqRecvInputs W st (wirePrekey :: body) rc).files
      (runAns S (pqRecvInputs W st (wirePrekey :: body) rc)) =
    pqxdhExpectedOutcome W (pqRecvInputs W st (wirePrekey :: body) rc)
      (d3PqRecvMatchingModel W st x g pm rc) := by
  rw [runAns_pqRecvPrekey_eq, hpksm, hparse, hS]; dsimp only
  have hpeer_id := idPeer_pqRecv W st (wirePrekey :: body) rc
  have hload := loadRec_pqRecv_eq hinj hcov st (wirePrekey :: body) rc hwf
  have hp_eq : initParty (addrValE st.party.other) = st.party := initParty_eq st.party
  have hcoins : pkRecvCoins (keyToBytes32 rc) = rc := pkRecvCoins_keyToBytes32 rc
  have htrust : StoresGhost.opened.identity.trusted cliIo.rd
      (runFiles (pqRecvInputs W st (wirePrekey :: body) rc))
      (addrValE st.party.other) pm.identityKey = .ok (st.trusts pm.identityKey) := by
    unfold IdGhost.trusted PqParty.trusts; rw [hpeer_id]; cases st.peerId <;> rfl
  have hsave : StoresGhost.opened.identity.saveUpd cliIo.rd
      (runFiles (pqRecvInputs W st (wirePrekey :: body) rc))
      (addrValE st.party.other) pm.identityKey =
      { StoresGhost.opened.identity with
        peers := StoresGhost.opened.identity.peers.put
          (addrValE st.party.other).name pm.identityKey.serialize } := by
    unfold IdGhost.saveUpd; rw [hpeer_id]
  rcases g with ⟨gp, gs0, gep, gce⟩
  have hg_party : gp = st.party := (hwf.1 x ⟨gp, gs0, gep, gce⟩ hsess).2.1
  subst hg_party
  unfold decPkDef d3PqRecvMatchingModel pqxdhExpectedOutcome; dsimp only
  rw [hload, hsess, htrust, hp_eq, hcoins]
  cases ht : st.trusts pm.identityKey with
  | false => rfl
  | true =>
    rw [show (!true) = false from rfl, ite_eq_right (c := false = true) Bool.noConfusion]
    dsimp only [Option.map_some, Option.bind_some, toRecord, extrasOf, toSessionExtras]
    have hmatch' : SessMatchesPm
        { state := gs0
          pendingPreKey := if gs0.pendingPreKey then some x.pending else none
          pendingKyberPreKey := if gs0.pendingPreKey then x.kyber else none
          localRegistrationId := x.localRegistrationId
          remoteRegistrationId := x.remoteRegistrationId
          aliceBaseKey := x.aliceBaseKey } pm := hmatch
    rw [ite_eq_left hmatch']
    by_cases hrem : gs0.remoteIdentity ≠ some pm.identityKey
    · rw [ite_eq_left hrem, ite_eq_left hrem]; rfl
    · rw [ite_eq_right hrem, ite_eq_right hrem]
      cases hdec : SessionState.tryDecryptFromRecord W.C (pqxdhSpqrSession W)
          ((pqxdhSessionParams W).expectedAddrs st.party) pm.message .preKey rc gs0 with
      | mk res st' =>
        cases res with
        | error err => cases err <;> rfl
        | ok pt =>
          dsimp only
          have hpend := (CryptoGames.LibsignalSessionApi.SessionState.tryDecryptFromRecord_ok
            W.C (pqxdhSpqrSession W) _ pm.message .preKey rc hdec).1
          have hclr := encodeRecord_cleared_eq_encodeRecordX x
            ⟨st.party, gs0, gep, gce⟩ st' hpend
          dsimp only [toRecord, extrasOf, toSessionExtras] at hclr
          rw [hsave, hclr]
          dsimp only [finish, Option.map_some, observe]
          refine congrArg (Outcome.exited 0 pt) ?_
          have hw := namedWrites_of_dirs st.party.other pm.identityKey.serialize
            (encodeRecordUnderExtras (fun _ => x)
              { party := st.party, session := st', epoch := gep, chainEpochs := gce })
            StoresGhost.opened.kyber.oneTime StoresGhost.opened.kyber.lastResort
            StoresGhost.opened.oneTime (w8 := []) (w9 := []) (w7 := [])
            ⟨fun _ h => False.elim (List.not_mem_nil h), rfl⟩
            ⟨fun _ h => False.elim (List.not_mem_nil h), rfl⟩
            ⟨fun _ h => False.elim (List.not_mem_nil h), rfl⟩
          rw [hw]
          exact filesOf_commit_master W st _ (wirePrekey :: body) rc _ rfl
            (fun _ h => by rw [List.mem_singleton] at h; subst h; exact recvBucket_identityFile _)
            (fun _ h => by rw [List.mem_singleton] at h; subst h; exact recvBucket_sessionFile _)
            (fun _ h => False.elim (List.not_mem_nil h))
            (fun _ h => False.elim (List.not_mem_nil h))
            (fun _ h => False.elim (List.not_mem_nil h))
            (fun _ h => False.elim (List.not_mem_nil h))
            (fun _ h => False.elim (List.not_mem_nil h))
            (fun _ h => False.elim (List.not_mem_nil h))
            rfl rfl rfl rfl rfl rfl
            (fun q => by rw [List.append_nil]; exact find?_self_double _ q)
            (fun q => by rw [List.append_nil]; exact find?_self_double _ q)
            (fun q => by rw [List.append_nil]; exact find?_self_double _ q)

/-! ## 2. `cliRunSemPathB`, `MainOkPathBD3F3`, and Two-Placement Whole-Process Lifts -/

/-- `RunSem` instantiated with `decPkDef`, `DecPkOkPathB`, and `pksmParse`. -/
noncomputable def cliRunSemPathB (X : UnreachedPqxdhPrimitives) (W : CliHooks) : RunSem :=
  cliRunSemF3 X W (decPkDef X ⟨W.C, W.Q⟩ scopeIn)
    (DecPkOkPathB ⟨W.C, W.Q⟩ scopeIn) pksmParse

/-- `runRel`, `observe`, and `CommitOk` at `cliRunSemPathB X W` on matching-session Path-B inputs. -/
theorem runRel_pqRecv_matchingPathB (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (st : PqParty) (x : RecordExtras) (g : GhostState (List (BitVec 8)))
    (body : List (BitVec 8)) (pm : PreKeySignalMessage) (rc : BitVec 256)
    (hwf : PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st) (hsess : st.session = some (x, g))
    (hlen : (wirePrekey :: body).length ≤ 2 ^ 32)
    (hparse : pksmParse body = some pm)
    (hmatch : SessMatchesPm (d3PqSessionOf x g) pm) :
    let WP : PEParams := ⟨W.C, W.Q⟩
    let inp := pqRecvInputs WP st (wirePrekey :: body) rc
    let a := runAns (cliRunSemPathB X W) inp
    runRel (cliRunSemPathB X W) inp a ∧
      observe inp.files a = pqxdhExpectedOutcome WP inp (d3PqRecvMatchingModel WP st x g pm rc) ∧
      CommitOk inp (MainResult.ofAnswer a) := by
  dsimp only
  let WP : PEParams := ⟨W.C, W.Q⟩
  exact ⟨⟨domainArgv_pqRecv WP st (wirePrekey :: body) rc,
      runBounds_pqRecv WP st (wirePrekey :: body) rc hlen,
      runFilesOk_pqRecv_cli_f3 (S := cliRunSemPathB X W) rfl WP st (wirePrekey :: body) rc hwf,
      runEncOk_pqRecv (cliRunSemPathB X W) WP st (wirePrekey :: body) rc,
      runHsOk_pqRecv_matchingPathB (cliRunSemPathB X W) WP scopeIn
        (fun _ _ _ _ h => h) rfl encodeInjOn_scopeIn (ratchetScopeCoversPq_scopeIn WP)
        st x g body pm rc hwf hsess hparse hmatch,
      rfl⟩,
    observe_runAns_pqRecv_matchingPathB (cliRunSemPathB X W) X WP scopeIn
      rfl rfl encodeInjOn_scopeIn (ratchetScopeCoversPq_scopeIn WP)
      st x g body pm rc hwf hsess hparse hmatch,
    commitOk_pqRecvPrekey_decPkDef (S := cliRunSemPathB X W) (X := X) (W := WP)
      (Scope := scopeIn) rfl st body rc⟩

/-- `NeedLocks` + `cliBudgetLimits` `main`-level specification for matching-session Path-B
pre-key `recv` scoped via `pqD3ScopedRun`. -/
def MainOkPathBD3F3
    (mpl mmpl : MultiPlacement) (CodeOk : Memory → Prop)
    (libcAddr brkStart : BitVec 64) (stk : Nat) : Prop :=
  mpl.base 547 ≠ 0#64 →
  ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks),
    ∀ (γ : GhostName) (tp : BitVec 64),
      subroutine_ok (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) (mpl.base 617)
        (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk
          (fineHookRustCliAllocBudget γ mmpl tp brkStart)
          cliBudgetLimits fineCostModel.init stk (cliStaticsPlacedAt mpl)
          (pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemPathB X W))) cliProcessInputs)

/-- Strict whole-process evaluation of `cliRunPlacedSig mpl mmpl elf W` on matching-session
Path-B pre-key `recv` inputs. -/
theorem d3_matchingPathB_strict_of_f3
    {mpl mmpl : MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop} {elf : ElfImage}
    (H : CliElfF3B2NeedLocksAssumptions mpl mmpl exitStk libcAddr stk CodeOk elf)
    (hpathB : MainOkPathBD3F3 mpl mmpl CodeOk libcAddr elf.brkStart stk)
    (W : CliHooks) (st : PqParty) (x : RecordExtras) (g : GhostState (List (BitVec 8)))
    (body : List (BitVec 8)) (pm : PreKeySignalMessage) (rc : BitVec 256)
    (hwf : PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st) (hsess : st.session = some (x, g))
    (hlen : (wirePrekey :: body).length ≤ 2 ^ 32)
    (hparse : pksmParse body = some pm)
    (hmatch : SessMatchesPm (d3PqSessionOf x g) pm) :
    let WP : PEParams := ⟨W.C, W.Q⟩
    let inp := pqRecvInputs WP st (wirePrekey :: body) rc
    cliRunPlacedSig mpl mmpl elf W inp =
      some (if (wirePrekey :: body).length > stdinCapBytes then .exited 2 [] (filesOf inp.files)
        else pqxdhExpectedOutcome WP inp (d3PqRecvMatchingModel WP st x g pm rc)) :=
  pqRecv_strict_obs_of_f3B2NeedLocks H (hpathB H.base547NeZero defaultExtrasF3 W) hwf (fun _ => by
    obtain ⟨hrun, hobs, hcommit⟩ :=
      runRel_pqRecv_matchingPathB defaultExtrasF3 W st x g body pm rc hwf hsess hlen hparse hmatch
    exact ⟨runAns (cliRunSemPathB defaultExtrasF3 W)
        (pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: body) rc),
      ⟨Or.inr ⟨st, wirePrekey :: body, rc, hwf, rfl⟩, hrun⟩, hobs, hcommit⟩)

/-- `OutcomeOrExcusedAbort (CliReachesOOMPlaced mpl mmpl elf W)` lift of
`d3_matchingPathB_strict_of_f3`, discharging `CliPqBinaryV2OomF3Placed.matchingPathB`. -/
theorem d3_matchingPathB_f3
    {mpl mmpl : MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop} {elf : ElfImage}
    (H : CliElfF3B2NeedLocksAssumptions mpl mmpl exitStk libcAddr stk CodeOk elf)
    (hpathB : MainOkPathBD3F3 mpl mmpl CodeOk libcAddr elf.brkStart stk) :
    ∀ (W : CliHooks) (st : PqParty) (x : RecordExtras)
      (g : GhostState (List (BitVec 8))) (body : List (BitVec 8))
      (pm : PreKeySignalMessage) (rc : BitVec 256),
      PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st → st.session = some (x, g) →
      (wirePrekey :: body).length ≤ 2 ^ 32 →
      pksmParse body = some pm → SessMatchesPm (d3PqSessionOf x g) pm →
      let WP : PEParams := ⟨W.C, W.Q⟩
      let inp := pqRecvInputs WP st (wirePrekey :: body) rc
      OutcomeOrExcusedAbort (CliReachesOOMPlaced mpl mmpl elf W)
        (cliRunPlacedSig mpl mmpl elf W) inp
        (· = if (wirePrekey :: body).length > stdinCapBytes then .exited 2 [] (filesOf inp.files)
          else pqxdhExpectedOutcome WP inp (d3PqRecvMatchingModel WP st x g pm rc)) :=
  fun W st x g body pm rc hwf hsess hlen hparse hmatch =>
    outcomeOrExcusedAbort_of_eq
      (d3_matchingPathB_strict_of_f3 H hpathB W st x g body pm rc hwf hsess hlen hparse hmatch)

end LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3MatchingPathBF3
