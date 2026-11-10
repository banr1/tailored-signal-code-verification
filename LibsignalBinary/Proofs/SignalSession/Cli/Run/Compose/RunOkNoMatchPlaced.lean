/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkNoMatchDefsPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.S0Lemmas.AgreeCommit
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.S0Lemmas.AgreeKeys
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.S0Lemmas.AgreePaths
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.S0Lemmas.AgreeStore
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.S0Lemmas.Agree
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Run
import all Init.Data.Repr
import Init.Data.String.Basic
import Init.Data.String.Defs
import Init.Data.ToString.Basic

@[expose] public section

set_option autoImplicit false

/-!
# Placed D2(c) `run`-Level `NoMatch` Agreement and `hrun_cli_d2c_placed`

Relocatable (`[LibsignalPlacement]`) counterparts of `RunOkNoMatch.lean`: proves exact 2-session
`d2cObserve_placed` agreement across all file paths, canonical-path `ObservedExceptNormPlaced`
outside `sessionFile (partyAddress peer)`, and `hrun_cli_d2c_placed` / `hrun_cli_d2c_tight_placed`.
-/

namespace CryptoVerification.SignalSession.Cli.RunProofs

open Arm64 Arm64.Process ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.E2E CryptoVerification.RecordCodecs
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.Run.Placed
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure

/-! ## 4. D2(c) `NoMatch` Commit Overwrite & Exact / `ObservedExceptNormPlaced` Agreement -/

theorem filesOf_commit_master_d2c_placed (W : PEParams) (st st' : PqParty)
    (c : List (BitVec 8)) (rc : BitVec 256)
    (ws : List (String × List (BitVec 8)))
    {w4 w5 w7 w8 w9 : List (String × List (BitVec 8))}
    {d2cBytes : List (BitVec 8)}
    (hws : ws = w4 ++ w8 ++ w9 ++ w7 ++ w5)
    (hw5_eq : w5 = [(sessionFile (partyAddress st.party.other), d2cBytes)])
    (hb4 : ∀ x ∈ w4, DecPkS0.recvBucket x.1 = 4)
    (hb7 : ∀ x ∈ w7, DecPkS0.recvBucket x.1 = 7)
    (hb8 : ∀ x ∈ w8, DecPkS0.recvBucket x.1 = 8)
    (hb9 : ∀ x ∈ w9, DecPkS0.recvBucket x.1 = 9)
    (hw7 : ∀ x ∈ w7, DecPkS0.IsRecvFile x.1)
    (hw8 : ∀ x ∈ w8, DecPkS0.IsRecvFile x.1)
    (hw9 : ∀ x ∈ w9, DecPkS0.IsRecvFile x.1)
    (hp_party : st'.party = st.party)
    (heq2 : DecPkS0.blockDir2 W st' = DecPkS0.blockDir2 W st)
    (heq3 : DecPkS0.blockDir3 st' = DecPkS0.blockDir3 st)
    (heq4 : w4 = DecPkS0.blockDir4 st')
    (heq6 : DecPkS0.blockDir6 W st' = DecPkS0.blockDir6 W st)
    (heq7 : ∀ q, (DecPkS0.blockDir7 W st ++ w7).reverse.find? (fun x => x.1 == q) =
      (DecPkS0.blockDir7 W st ++ DecPkS0.blockDir7 W st').reverse.find? (fun x => x.1 == q))
    (heq8 : ∀ q, (DecPkS0.blockDir8 st ++ w8).reverse.find? (fun x => x.1 == q) =
      (DecPkS0.blockDir8 st ++ DecPkS0.blockDir8 st').reverse.find? (fun x => x.1 == q))
    (heq9 : ∀ q, (DecPkS0.blockDir9 st ++ w9).reverse.find? (fun x => x.1 == q) =
      (DecPkS0.blockDir9 st ++ DecPkS0.blockDir9 st').reverse.find? (fun x => x.1 == q)) :
    filesOf ((pqRecvInputs W st c rc).files ++ ws) =
      filesOf (((pqRecvInputs W st c rc).files ++ encodeDir W st') ++ w5) := by
  have heq1 : DecPkS0.blockDir1 st' = DecPkS0.blockDir1 st := by
    simp only [DecPkS0.blockDir1, hp_party]
  have hb5 : ∀ x ∈ w5, DecPkS0.recvBucket x.1 = 5 := by
    intro x hx; rw [hw5_eq, List.mem_singleton] at hx; subst hx
    exact DecPkS0.recvBucket_sessionFile _
  have hw5 : ∀ x ∈ w5, DecPkS0.IsRecvFile x.1 := by
    intro x hx; rw [hw5_eq, List.mem_singleton] at hx; subst hx
    exact DecPkS0.isRecvFile_sessionFile _
  apply DecPkS0.filesOf_eq_of_isRecvFile
  · intro x hx
    simp only [hws, List.mem_append, or_assoc] at hx
    rcases hx with henc | h4 | h8 | h9 | h7 | h5
    · exact DecPkS0.isRecvFile_pqRecv_files W st c rc x henc
    · rw [heq4] at h4
      exact DecPkS0.isRecvFile_encodeDir W st' x (by rw [DecPkS0.encodeDir_blocks]; simp [h4])
    · exact hw8 x h8
    · exact hw9 x h9
    · exact hw7 x h7
    · exact hw5 x h5
  · intro x hx
    rcases List.mem_append.mp hx with hpre | h5
    · rcases List.mem_append.mp hpre with henc | henc'
      · exact DecPkS0.isRecvFile_pqRecv_files W st c rc x henc
      · exact DecPkS0.isRecvFile_encodeDir W st' x henc'
    · exact hw5 x h5
  · intro q
    refine congrArg (Option.map Prod.snd) ?_
    obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9⟩ := DecPkS0.bucket_blockDir W st
    obtain ⟨d1', d2', d3', d4', d5', d6', d7', d8', d9'⟩ := DecPkS0.bucket_blockDir W st'
    let nilE : List (String × List (BitVec 8)) := []
    have hws_perm : (w4 ++ w8 ++ w9 ++ w7 ++ w5).reverse.find? (fun x => x.1 == q) =
        (nilE ++ nilE ++ nilE ++ w4 ++ w5 ++ nilE ++ w7 ++ w8 ++ w9).reverse.find?
          (fun x => x.1 == q) := by
      simp only [nilE, List.nil_append, List.reverse_append, List.find?_append]
      have n4 : DecPkS0.recvBucket q ≠ 4 → w4.reverse.find? (fun x => x.1 == q) = none := fun h =>
        DecPkS0.find?_rev_none fun x hx => by rw [hb4 x hx]; exact Ne.symm h
      have n5 : DecPkS0.recvBucket q ≠ 5 → w5.reverse.find? (fun x => x.1 == q) = none := fun h =>
        DecPkS0.find?_rev_none fun x hx => by rw [hb5 x hx]; exact Ne.symm h
      have n7 : DecPkS0.recvBucket q ≠ 7 → w7.reverse.find? (fun x => x.1 == q) = none := fun h =>
        DecPkS0.find?_rev_none fun x hx => by rw [hb7 x hx]; exact Ne.symm h
      have n8 : DecPkS0.recvBucket q ≠ 8 → w8.reverse.find? (fun x => x.1 == q) = none := fun h =>
        DecPkS0.find?_rev_none fun x hx => by rw [hb8 x hx]; exact Ne.symm h
      have n9 : DecPkS0.recvBucket q ≠ 9 → w9.reverse.find? (fun x => x.1 == q) = none := fun h =>
        DecPkS0.find?_rev_none fun x hx => by rw [hb9 x hx]; exact Ne.symm h
      match hb : DecPkS0.recvBucket q with
      | 4 => simp [n5 (by omega), n7 (by omega), n8 (by omega), n9 (by omega)]
      | 5 => simp [n4 (by omega), n7 (by omega), n8 (by omega), n9 (by omega)]
      | 7 => simp [n4 (by omega), n5 (by omega), n8 (by omega), n9 (by omega)]
      | 8 => simp [n4 (by omega), n5 (by omega), n7 (by omega), n9 (by omega)]
      | 9 => simp [n4 (by omega), n5 (by omega), n7 (by omega), n8 (by omega)]
      | 0 | 1 | 2 | 3 | 6 | _ + 10 =>
        simp [n4 (by omega), n5 (by omega), n7 (by omega), n8 (by omega), n9 (by omega)]
    rw [hws]
    have hlhs : ((pqRecvInputs W st c rc).files ++ (w4 ++ w8 ++ w9 ++ w7 ++ w5)).reverse.find?
        (fun x => x.1 == q) =
        ((nilE ++ nilE ++ nilE ++ w4 ++ w5 ++ nilE ++ w7 ++ w8 ++ w9).reverse.find?
          (fun x => x.1 == q)).or
          ((encodeDir W st ++ [(coinsFile, HMAC.keyToBytes32 rc)]).reverse.find?
            (fun x => x.1 == q)) := by
      simp only [pqRecvInputs, pqInputs, List.append_nil]
      rw [List.reverse_append, List.find?_append, hws_perm]
    have hrhs : (((pqRecvInputs W st c rc).files ++ encodeDir W st') ++ w5).reverse.find?
        (fun x => x.1 == q) =
        (w5.reverse.find? (fun x => x.1 == q)).or
          (((DecPkS0.blockDir1 st' ++ DecPkS0.blockDir2 W st' ++ DecPkS0.blockDir3 st' ++
             DecPkS0.blockDir4 st' ++ DecPkS0.blockDir5 st' ++ DecPkS0.blockDir6 W st' ++
             DecPkS0.blockDir7 W st' ++ DecPkS0.blockDir8 st' ++ DecPkS0.blockDir9 st').reverse.find?
            (fun x => x.1 == q)).or
            ((encodeDir W st ++ [(coinsFile, HMAC.keyToBytes32 rc)]).reverse.find?
              (fun x => x.1 == q))) := by
      have hfiles : (pqRecvInputs W st c rc).files =
          encodeDir W st ++ [(coinsFile, HMAC.keyToBytes32 rc)] := by
        simp only [pqRecvInputs, pqInputs, List.append_nil]
      rw [hfiles, List.reverse_append, List.find?_append, List.reverse_append, List.find?_append,
        DecPkS0.encodeDir_blocks W st']
    have hnilE : ∀ n : Nat, ∀ x ∈ nilE, DecPkS0.recvBucket x.1 = n :=
      fun _ _ h => False.elim (List.not_mem_nil h)
    rw [hlhs, hrhs]
    rw [DecPkS0.find?_select_block (hnilE 1) (hnilE 2) (hnilE 3) hb4 hb5 (hnilE 6) hb7 hb8 hb9 q,
      DecPkS0.find?_select_block d1' d2' d3' d4' d5' d6' d7' d8' d9' q]
    by_cases h5q : DecPkS0.recvBucket q = 5
    · rw [h5q]
      rw [hw5_eq]
      by_cases hsq : sessionFile (partyAddress st.party.other) = q
      · subst hsq; simp
      · have hw5_none : ([(sessionFile (partyAddress st.party.other), d2cBytes)] :
            List (String × List (BitVec 8))).reverse.find? (fun x => x.1 == q) = none := by
          simp [beq_false_of_ne hsq]
        have hb5'_none : (DecPkS0.blockDir5 st').reverse.find? (fun x => x.1 == q) = none := by
          unfold DecPkS0.blockDir5
          rw [hp_party]
          cases st'.session <;> simp [beq_false_of_ne hsq]
        rw [hw5_none, hb5'_none]
        simp only [Option.none_or]
    · have hw5_none : w5.reverse.find? (fun x => x.1 == q) = none :=
        DecPkS0.find?_rev_none fun x hx => by rw [hb5 x hx]; exact Ne.symm h5q
      rw [hw5_none, Option.none_or]
      by_cases h10 : DecPkS0.recvBucket q = 10
      · rw [h10]; rfl
      · have hc_none : ([(coinsFile, HMAC.keyToBytes32 rc)] :
            List (String × List (BitVec 8))).reverse.find? (fun x => x.1 == q) = none :=
          DecPkS0.find?_rev_none fun x hx => by
            rw [List.mem_singleton] at hx; subst hx; rw [DecPkS0.recvBucket_coins]; exact Ne.symm h10
        simp only [List.reverse_append, List.find?_append, hc_none, Option.none_or]
        rw [DecPkS0.encodeDir_blocks W st,
          DecPkS0.find?_select_block d1 d2 d3 d4 d5 d6 d7 d8 d9 q]
        match hb : DecPkS0.recvBucket q with
        | 1 =>
          simp only [nilE, List.reverse_nil, List.find?_nil, Option.none_or, heq1,
            ← List.find?_append, ← List.reverse_append]
          exact DecPkS0.find?_self_double _ q
        | 2 =>
          simp only [nilE, List.reverse_nil, List.find?_nil, Option.none_or, heq2,
            ← List.find?_append, ← List.reverse_append]
          exact DecPkS0.find?_self_double _ q
        | 3 =>
          simp only [nilE, List.reverse_nil, List.find?_nil, Option.none_or, heq3,
            ← List.find?_append, ← List.reverse_append]
          exact DecPkS0.find?_self_double _ q
        | 4 => rw [heq4]; rfl
        | 5 => exact absurd hb h5q
        | 6 =>
          simp only [nilE, List.reverse_nil, List.find?_nil, Option.none_or, heq6,
            ← List.find?_append, ← List.reverse_append]
          exact DecPkS0.find?_self_double _ q
        | 7 => simpa only [List.reverse_append, List.find?_append] using heq7 q
        | 8 => simpa only [List.reverse_append, List.find?_append] using heq8 q
        | 9 => simpa only [List.reverse_append, List.find?_append] using heq9 q
        | 0 => rfl
        | _ + 10 => rfl

/-- Converse of `DecPkS0.sessMatchesPm_toRecord` on a version-4 session: if `SessMatchesPm` holds
on `sessionOfX (fun _ => x) g` at `pmOfE m inner` and `g.session.sessionVersion = 4#32`, then
`PqSessionMatches x g m` holds. -/
theorem pqSessionMatches_of_sessMatchesPm_placed (x : RecordExtras) (g : GhostState E2E.Bytes)
    (m : PreKeyMessageFields) (inner : SignalMessage)
    (hver : g.session.sessionVersion = 4#32)
    (hm : SessMatchesPm (E2E.RecordX.sessionOfX (fun _ => x) g) (pmOfE m inner)) :
    PqSessionMatches x g m :=
  ⟨hm.2, hver⟩

/-- When `st.session = some (x₀, g₀)` and `¬ PqSessionMatches x₀ g₀ m`, `observe` of `runAns S` at
`decPkDefD2c` equals `d2cObserve_placed` of `pqRecvPrekeyModel X W { st with session := none } m rc`
at all file paths (including `sessionFile (partyAddress st.party.other)`). -/
theorem runAns_pqRecvPrekey_noMatch_exact_placed (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hS : S.decryptPrekey = decPkDefD2c X W Scope)
    (hP : RunRefine.PksmParseAgrees S)
    (hpksm : PksmTyped S)
    (hinj : Slots.EncodeInjOn Scope) (hcov : ScopeCoversPq W Scope)
    (st : PqParty) (x₀ : RecordExtras) (g₀ : GhostState E2E.Bytes)
    (m : PreKeyMessageFields) (rc : BitVec 256)
    (hwf : PqxdhPartyInSpecDomain W st) (hs : st.session = some (x₀, g₀))
    (hm : m.inner.length + 2048 < 2 ^ 32)
    (hnot : ¬ PqSessionMatches x₀ g₀ m) :
    observe (pqRecvInputs W st (wirePrekey :: m.bytes) rc).files
        (runAns S (pqRecvInputs W st (wirePrekey :: m.bytes) rc)) =
      d2cObserve_placed W (pqRecvInputs W st (wirePrekey :: m.bytes) rc) st.party.other x₀ g₀
        (pqRecvPrekeyModel X W { st with session := none } m rc) := by
  rw [RunRefine.runAns_pqRecvPrekey_eq]
  cases hp : S.pksmParse m.bytes with
  | none =>
    unfold pqRecvPrekeyModel d2cObserve_placed
    cases hi : SignalMessage.tryFrom protoSignalCodec m.inner with
    | error _ => rfl
    | ok inner => exact absurd hi (hP m hm hp inner)
  | some pm =>
    obtain ⟨inner, htry, rfl⟩ := hpksm m pm hm hp
    have hpeer_id := DecPkS0.idPeer_pqRecv W st (wirePrekey :: m.bytes) rc
    have hload := DecPkS0.loadRec_pqRecv_eq hinj hcov st (wirePrekey :: m.bytes) rc hwf
    rw [hs] at hload
    dsimp only [Option.map_some] at hload
    have hp_eq : initParty (RunRefine.addrValE st.party.other) = st.party :=
      InitS0.initParty_eq st.party
    have hcoins : pkRecvCoins (HMAC.keyToBytes32 rc) = rc := DecPkS0.pkRecvCoins_keyToBytes32 rc
    have htrust : StoresGhost.opened.identity.trusted cliIo.rd
        (runFiles (pqRecvInputs W st (wirePrekey :: m.bytes) rc))
        (RunRefine.addrValE st.party.other) (pmOfE m inner).identityKey =
        .ok (st.trusts ⟨⟨m.idPub⟩⟩) := by
      unfold IdGhost.trusted PqParty.trusts
      rw [hpeer_id]
      cases st.peerId <;> rfl
    have hsave : StoresGhost.opened.identity.saveUpd cliIo.rd
        (runFiles (pqRecvInputs W st (wirePrekey :: m.bytes) rc))
        (RunRefine.addrValE st.party.other) (⟨⟨m.idPub⟩⟩ : IdentityKey) =
        { StoresGhost.opened.identity with
          peers := StoresGhost.opened.identity.peers.put
            (RunRefine.addrValE st.party.other).name (⟨⟨m.idPub⟩⟩ : IdentityKey).serialize } := by
      unfold IdGhost.saveUpd
      rw [hpeer_id]
    obtain ⟨⟨g_reach, hreach, _, hsess⟩, _⟩ := hwf.1 x₀ g₀ hs
    have hver4 : g₀.session.sessionVersion = 4#32 := hsess ▸ reachPq_sessionVersion_placed hreach
    have hnot_pm : ¬ SessMatchesPm (E2E.RecordX.sessionOfX (fun _ => x₀) g₀) (pmOfE m inner) :=
      fun hm_pm => hnot (pqSessionMatches_of_sessMatchesPm_placed x₀ g₀ m inner hver4 hm_pm)
    dsimp only
    rw [hS]
    unfold pqRecvPrekeyModel d2cObserve_placed
    rw [htry]
    dsimp only
    have htr_eq : ({ st with session := none } : PqParty).trusts ⟨⟨m.idPub⟩⟩ =
        st.trusts ⟨⟨m.idPub⟩⟩ := rfl
    rw [htr_eq]
    cases ht : st.trusts ⟨⟨m.idPub⟩⟩ with
    | false =>
      rw [decPkDefD2c_eq_decPkDef_of_untrusted X W Scope _ _ _ _ _
        (by rw [htrust, ht]; intro h; cases h)]
      unfold decPkDef
      dsimp only
      rw [hload, htrust, ht]
      rfl
    | true =>
      rw [show (!true) = false from rfl, ite_eq_right (c := false = true) Bool.noConfusion]
      rw [decPkDefD2c_of_not_match X W Scope _ _ _ _ _ hload rfl (htrust.trans (by rw [ht])) hnot_pm]
      unfold decPkAcceptWith
      dsimp only
      rw [pkToE?_pmOfE m inner htry]
      dsimp only
      have hpksk : pkStoreKeys (runFiles (pqRecvInputs W st (wirePrekey :: m.bytes) rc)) m =
          preKeysNamedBy st m :=
        DecPkS0.pkStoreKeys_pqRecv W st (wirePrekey :: m.bytes) rc hwf m
      rw [hpksk, DecPkS0.keyPair_pqRecv W st (wirePrekey :: m.bytes) rc,
        DecPkS0.regId_pqRecv W st (wirePrekey :: m.bytes) rc, hp_eq, hcoins]
      have hkeys_eq : preKeysNamedBy { st with session := none } m = preKeysNamedBy st m := rfl
      rw [hkeys_eq]
      cases hkeys : preKeysNamedBy st m with
      | none => rfl
      | some k =>
        dsimp only
        rw [DecPkS0.recvPrekeyState_clampScalar]
        cases hrecv : recvPrekeyState X W st.party st.me k m rc with
        | none => rfl
        | some o =>
          cases o with
          | none => rfl
          | some triple =>
            rcases triple with ⟨x', gs, pt⟩
            dsimp only
            have hlr_some :
                List.lookup m.kpkId st.kyberOneTime = none ∨
                List.lookup m.kpkId st.kyberOneTime = some none →
                (List.lookup m.kpkId st.kyberLastResort).isSome := by
              intro hno
              unfold preKeysNamedBy at hkeys
              cases hspk : List.lookup m.spkId st.signed with
              | none => rw [hspk] at hkeys; nomatch hkeys
              | some s0 =>
                rw [hspk] at hkeys
                rcases hno with hn | hn <;> rw [hn] at hkeys
                · cases hlr : List.lookup m.kpkId st.kyberLastResort with
                  | none => simp [hlr] at hkeys
                  | some _ => rfl
                · cases hlr : List.lookup m.kpkId st.kyberLastResort with
                  | none => simp [hlr] at hkeys
                  | some _ => rfl
            have hspk_id : (pmOfE m inner).signedPreKeyId = m.spkId := rfl
            have hbk_eq : (pmOfE m inner).baseKey = ⟨m.baseKey⟩ := rfl
            have hopk_eq : (pmOfE m inner).preKeyId = m.opkId := rfl
            have hid_eq : (pmOfE m inner).identityKey = ⟨⟨m.idPub⟩⟩ := rfl
            rw [hspk_id, hbk_eq]
            have hmark := DecPkS0.kyberMark_pqRecv W st (wirePrekey :: m.bytes) rc hwf m hlr_some
            cases hkm : StoresGhost.opened.kyber.mark cliIo.rd
                (runFiles (pqRecvInputs W st (wirePrekey :: m.bytes) rc))
                m.kpkId m.spkId ⟨m.baseKey⟩ with
            | mk kres kyber' =>
              have hmk_none_eq : markKyberUsed { st with session := none } m =
                  (markKyberUsed st m).map (fun s1 => { s1 with session := none }) := by
                unfold markKyberUsed
                cases List.lookup m.kpkId st.kyberOneTime with
                | none =>
                  cases List.lookup m.kpkId st.kyberLastResort with
                  | none => rfl
                  | some ks =>
                    rcases ks with ⟨_, seen⟩
                    dsimp only
                    split <;> rfl
                | some ov =>
                  cases ov with
                  | none =>
                    cases List.lookup m.kpkId st.kyberLastResort with
                    | none => rfl
                    | some ks =>
                      rcases ks with ⟨_, seen⟩
                      dsimp only
                      split <;> rfl
                  | some _ => rfl
              rw [hmk_none_eq]
              cases hm_mod : markKyberUsed st m with
              | none =>
                rw [hkm, hm_mod] at hmark
                cases kres with
                | error _ => rfl
                | ok _ => nomatch hmark
              | some st1 =>
                rw [hkm, hm_mod] at hmark
                cases kres with
                | error _ => nomatch hmark
                | ok _ =>
                  dsimp only [Option.map_some, finish, observe]
                  have hrem_sess_eq :
                      ({ removeOpk { st1 with session := none } m with
                         peerId := some ⟨⟨m.idPub⟩⟩, session := some (x', gs) } : PqParty) =
                      { removeOpk st1 m with
                        peerId := some ⟨⟨m.idPub⟩⟩, session := some (x', gs) } := by
                    unfold removeOpk
                    cases m.opkId <;> rfl
                  have hd2c_bytes :
                      encodeRecordUnderExtras (fun _ => x') gs ++
                        E2E.Record.lenField 2
                          (E2E.Record.encSession
                            (Over.clearPending
                              { state := g₀.session
                                pendingPreKey :=
                                  if g₀.session.pendingPreKey = true then
                                    some (E2E.RecordX.extrasOf (fun _ => x₀) g₀.party).pending
                                  else none
                                pendingKyberPreKey :=
                                  if g₀.session.pendingPreKey = true then
                                    (E2E.RecordX.extrasOf (fun _ => x₀) g₀.party).kyber
                                  else none
                                localRegistrationId :=
                                  (E2E.RecordX.extrasOf (fun _ => x₀) g₀.party).localRegistrationId
                                remoteRegistrationId :=
                                  (E2E.RecordX.extrasOf (fun _ => x₀) g₀.party).remoteRegistrationId
                                aliceBaseKey :=
                                  (E2E.RecordX.extrasOf (fun _ => x₀) g₀.party).aliceBaseKey })) =
                        d2cRecordBytes_placed x' x₀ gs g₀ := by
                    change encodeRecordUnderExtras (fun _ => x') gs ++
                        E2E.Record.lenField 2
                          (E2E.Record.encSession
                            (Over.clearPending
                              (E2E.RecordX.sessionOfX (fun _ => x₀) g₀))) =
                      d2cRecordBytes_placed x' x₀ gs g₀
                    rw [encSession_clearPending_sessionOfX_eq x₀ g₀]
                    rfl
                  rw [hrem_sess_eq, hopk_eq, hid_eq, hsave, hd2c_bytes]
                  change Outcome.exited 0 pt _ = Outcome.exited 0 pt
                    (filesOf (((pqRecvInputs W st (wirePrekey :: m.bytes) rc).files ++
                      encodeDir W { removeOpk st1 m with
                        peerId := some ⟨⟨m.idPub⟩⟩, session := some (x', gs) }) ++
                      [(sessionFile (partyAddress st.party.other), d2cRecordBytes_placed x' x₀ gs g₀)]))
                  refine congrArg (Outcome.exited 0 pt) ?_
                  have hopk_upd :
                      ∃ (w7 : List (String × List (BitVec 8))) (otDir : DirGhost),
                        (m.opkId = none → otDir = StoresGhost.opened.oneTime) ∧
                        (∀ j, m.opkId = some j →
                          otDir = (removePreKey cliIo.rd
                            (runFiles (pqRecvInputs W st (wirePrekey :: m.bytes) rc))
                            StoresGhost.opened.oneTime j).2) ∧
                        ((∀ pw ∈ otDir.writes, ∀ bt ∈ pw.1, bt.toNat < 128) ∧
                         otDir.writes.map (fun pw => (pathStr pw.1, pw.2)) = w7) ∧
                        (∀ z ∈ w7, DecPkS0.recvBucket z.1 = 7) ∧
                        (∀ z ∈ w7, DecPkS0.IsRecvFile z.1) ∧
                        ((removeOpk st1 m).oneTime = (removeOpk st m).oneTime →
                          st1.oneTime = st.oneTime →
                          ∀ q, (DecPkS0.blockDir7 W st ++ w7).reverse.find? (fun u => u.1 == q) =
                            (DecPkS0.blockDir7 W st ++ DecPkS0.blockDir7 W (removeOpk st1 m)).reverse.find?
                              (fun u => u.1 == q)) := by
                    cases hopk : m.opkId with
                    | none =>
                      refine ⟨[], StoresGhost.opened.oneTime, ?_, ?_,
                        ⟨fun _ h => False.elim (List.not_mem_nil h), rfl⟩,
                        fun _ h => False.elim (List.not_mem_nil h),
                        fun _ h => False.elim (List.not_mem_nil h), fun _ hst1 q => ?_⟩
                      · intro _; rfl
                      · intro _ h; nomatch h
                      · have h7eq : DecPkS0.blockDir7 W (removeOpk st1 m) =
                            DecPkS0.blockDir7 W st := by
                          simp only [removeOpk, hopk, DecPkS0.blockDir7, hst1]
                        rw [h7eq, List.append_nil]
                        exact DecPkS0.find?_self_double _ q
                    | some j =>
                      have hsk_ex : ∃ sk, List.lookup j st.oneTime = some (some sk) := by
                        rw [DecPkS0.keysFor_eq] at hkeys
                        cases hspk : List.lookup m.spkId st.signed with
                        | none => rw [hspk] at hkeys; nomatch hkeys
                        | some s0 =>
                          rw [hspk] at hkeys
                          cases hkyb : DecPkS0.kyberLookup st m.kpkId with
                          | none => rw [hkyb] at hkeys; nomatch hkeys
                          | some kv =>
                            rw [hkyb, hopk] at hkeys
                            dsimp only at hkeys
                            cases hotl : List.lookup j st.oneTime with
                            | none => simp [hotl] at hkeys
                            | some ov =>
                              cases ov with
                              | none => simp [hotl] at hkeys
                              | some sk => exact ⟨sk, rfl⟩
                      obtain ⟨sk, hsk⟩ := hsk_ex
                      have hrem_ot := DecPkS0.removePreKey_pqRecv W st (wirePrekey :: m.bytes) rc
                        hwf.2.2.2.1 hsk
                      obtain ⟨hot_str, hot_asc⟩ := DecPkS0.oneTime_path_eq j
                      refine ⟨[(oneTimePreKeyFile j, [])],
                        StoresGhost.opened.oneTime.put (keyName j) [], ?_, ?_,
                        ⟨?_, ?_⟩, ?_, ?_, fun _ hst1 q => ?_⟩
                      · intro h; nomatch h
                      · intro j' hj'; cases hj'; exact hrem_ot.symm
                      · intro pw hpw bt hbt
                        change pw ∈ ((DirGhost.new _).put _ _).writes at hpw
                        rw [DecPkS0.new_put_writes, List.mem_singleton] at hpw
                        subst hpw; exact hot_asc bt hbt
                      · change ((DirGhost.new _).put _ _).writes.map _ = _
                        rw [DecPkS0.new_put_writes, List.map_cons, List.map_nil, hot_str]
                      · intro z hz
                        rw [List.mem_singleton] at hz; subst hz
                        exact DecPkS0.recvBucket_oneTimePreKey j
                      · intro z hz
                        rw [List.mem_singleton] at hz; subst hz
                        exact DecPkS0.isRecvFile_oneTimePreKey j
                      · have hm0 : (j, some sk) ∈ st.oneTime := DecPkS0.mem_of_lookup_eq_some hsk
                        have h7' : DecPkS0.blockDir7 W (removeOpk st1 m) =
                            ((st.oneTime.map (fun (i, a) =>
                              if i = j then (i, none) else (i, a))).map (fun (i, a) =>
                              (oneTimePreKeyFile i,
                                match a with
                                | some s => oneTimeRecordBytes W.C i s
                                | none => []))) := by
                          simp only [removeOpk, hopk, DecPkS0.blockDir7, hst1]; rfl
                        rw [h7']
                        exact DecPkS0.find?_map_update DecPkS0.oneTimePreKeyFile_inj hm0
                          (fun i a => match a with
                            | some s => oneTimeRecordBytes W.C i s | none => [])
                          none [] rfl q
                  obtain ⟨w7, otDir, hot_none, hot_some, hot_wr, hb7, hw7, heq7_fn⟩ := hopk_upd
                  suffices hcommit : filesOf
                      ((pqRecvInputs W st (wirePrekey :: m.bytes) rc).files ++
                        namedWrites
                          ({ StoresGhost.opened with
                             identity := { StoresGhost.opened.identity with
                               peers := StoresGhost.opened.identity.peers.put
                                 (RunRefine.addrValE st.party.other).name
                                 (⟨⟨m.idPub⟩⟩ : IdentityKey).serialize }
                             kyber := kyber'
                             oneTime := otDir
                             sessions := StoresGhost.opened.sessions.put
                               (addressText (RunRefine.addrValE st.party.other))
                               (d2cRecordBytes_placed x' x₀ gs g₀) }).writes) =
                      filesOf
                        (((pqRecvInputs W st (wirePrekey :: m.bytes) rc).files ++
                          encodeDir W
                            { removeOpk st1 m with
                              peerId := some ⟨⟨m.idPub⟩⟩, session := some (x', gs) }) ++
                          [(sessionFile (partyAddress st.party.other), d2cRecordBytes_placed x' x₀ gs g₀)]) by
                    cases hopk0 : m.opkId
                    · dsimp only; rw [hot_none hopk0] at hcommit; exact hcommit
                    · next j0 => dsimp only; rw [hot_some j0 hopk0] at hcommit; exact hcommit
                  rcases hmark with ⟨k1, hkot1, rfl, rfl⟩ | ⟨k2, seen, hklr2, _, rfl, rfl⟩
                  · dsimp only
                    obtain ⟨hkot_str, hkot_asc⟩ := DecPkS0.kyberOneTime_path_eq m.kpkId
                    have hw := DecPkS0.namedWrites_of_dirs st.party.other
                      (⟨⟨m.idPub⟩⟩ : IdentityKey).serialize
                      (d2cRecordBytes_placed x' x₀ gs g₀)
                      (StoresGhost.opened.kyber.oneTime.put (keyName m.kpkId) [])
                      StoresGhost.opened.kyber.lastResort
                      otDir
                      (w8 := [(oneTimeKyberPreKeyFile m.kpkId, [])])
                      (w9 := [])
                      (w7 := w7)
                      ⟨fun pw hpw bt hbt => by
                         change pw ∈ ((DirGhost.new _).put _ _).writes at hpw
                         rw [DecPkS0.new_put_writes, List.mem_singleton] at hpw
                         subst hpw; exact hkot_asc bt hbt,
                       by change ((DirGhost.new _).put _ _).writes.map _ = _
                          rw [DecPkS0.new_put_writes, List.map_cons, List.map_nil, hkot_str]⟩
                      ⟨fun _ h => False.elim (List.not_mem_nil h), rfl⟩
                      hot_wr
                    rw [hw]
                    have hparty_eq : ∀ q,
                        (DecPkS0.blockDir7 W st ++ w7).reverse.find? (fun u => u.1 == q) =
                          (DecPkS0.blockDir7 W st ++ DecPkS0.blockDir7 W
                            { removeOpk
                                { st with kyberOneTime := st.kyberOneTime.map (fun (i, k) =>
                                    if i = m.kpkId then (i, none) else (i, k)) } m with
                              peerId := some ⟨⟨m.idPub⟩⟩, session := some (x', gs) }).reverse.find?
                            (fun u => u.1 == q) := by
                      intro q
                      have hsame_ot :
                          (removeOpk
                            { st with kyberOneTime := st.kyberOneTime.map (fun (i, k) =>
                                if i = m.kpkId then (i, none) else (i, k)) } m).oneTime =
                          (removeOpk st m).oneTime := by
                        unfold removeOpk; cases m.opkId <;> rfl
                      exact heq7_fn hsame_ot rfl q
                    have hm_kot : (m.kpkId, some k1) ∈ st.kyberOneTime :=
                      DecPkS0.mem_of_lookup_eq_some hkot1
                    have h8_rem : ∀ st0 : PqParty,
                        (removeOpk st0 m).kyberOneTime = st0.kyberOneTime := by
                      intro st0; unfold removeOpk; cases m.opkId <;> rfl
                    have h9_rem : ∀ st0 : PqParty,
                        (removeOpk st0 m).kyberLastResort = st0.kyberLastResort := by
                      intro st0; unfold removeOpk; cases m.opkId <;> rfl
                    have h1_rem : ∀ st0 : PqParty, (removeOpk st0 m).party = st0.party := by
                      intro st0; unfold removeOpk; cases m.opkId <;> rfl
                    have h2_rem : ∀ st0 : PqParty, (removeOpk st0 m).me = st0.me := by
                      intro st0; unfold removeOpk; cases m.opkId <;> rfl
                    have h6_rem : ∀ st0 : PqParty, (removeOpk st0 m).signed = st0.signed := by
                      intro st0; unfold removeOpk; cases m.opkId <;> rfl
                    exact filesOf_commit_master_d2c_placed W st _ (wirePrekey :: m.bytes) rc _ rfl rfl
                      (fun _ h => by
                        rw [List.mem_singleton] at h; subst h
                        exact DecPkS0.recvBucket_identityFile _)
                      hb7
                      (fun _ h => by
                        rw [List.mem_singleton] at h; subst h
                        exact DecPkS0.recvBucket_oneTimeKyberPreKey _)
                      (fun _ h => False.elim (List.not_mem_nil h))
                      hw7
                      (fun _ h => by
                        rw [List.mem_singleton] at h; subst h
                        exact DecPkS0.isRecvFile_oneTimeKyberPreKey _)
                      (fun _ h => False.elim (List.not_mem_nil h))
                      (by simp only [h1_rem])
                      (by simp only [DecPkS0.blockDir2, h2_rem])
                      (by simp only [DecPkS0.blockDir3, h2_rem])
                      (by simp only [DecPkS0.blockDir4, h1_rem])
                      (by simp only [DecPkS0.blockDir6, h6_rem])
                      hparty_eq
                      (fun q => by
                        have h8' : DecPkS0.blockDir8
                            { removeOpk
                                { st with kyberOneTime := st.kyberOneTime.map (fun (i, k) =>
                                    if i = m.kpkId then (i, none) else (i, k)) } m with
                              peerId := some ⟨⟨m.idPub⟩⟩, session := some (x', gs) } =
                            ((st.kyberOneTime.map (fun (i, a) =>
                              if i = m.kpkId then (i, none) else (i, a))).map (fun (i, a) =>
                              (oneTimeKyberPreKeyFile i,
                                match a with
                                | some kv => kyberRecordBytes i kv
                                | none => []))) := by
                          simp only [DecPkS0.blockDir8, h8_rem]; rfl
                        rw [h8']
                        exact DecPkS0.find?_map_update DecPkS0.oneTimeKyberPreKeyFile_inj hm_kot
                          (fun i a => match a with
                            | some kv => kyberRecordBytes i kv | none => [])
                          none [] rfl q)
                      (fun q => by
                        have h9' : DecPkS0.blockDir9
                            { removeOpk
                                { st with kyberOneTime := st.kyberOneTime.map (fun (i, k) =>
                                    if i = m.kpkId then (i, none) else (i, k)) } m with
                              peerId := some ⟨⟨m.idPub⟩⟩, session := some (x', gs) } =
                            DecPkS0.blockDir9 st := by
                          simp only [DecPkS0.blockDir9, h9_rem]
                        rw [h9', List.append_nil]
                        exact DecPkS0.find?_self_double _ q)
                  · dsimp only
                    obtain ⟨_, _, _, _, _, hnd_klr⟩ := hwf
                    have hm_klr : (m.kpkId, (k2, seen)) ∈ st.kyberLastResort :=
                      DecPkS0.mem_of_lookup_eq_some hklr2
                    have huniq_seen : ∀ {l : List (BitVec 32 × PqKyberKey ×
                        List (BitVec 32 × List.Vector (BitVec 8) 32))},
                        (l.map Prod.fst).Nodup →
                        (m.kpkId, (k2, seen)) ∈ l →
                        ∀ {k s}, (m.kpkId, (k, s)) ∈ l → s = seen := by
                      intro l hnd hm1 k s hm2
                      induction l with
                      | nil => nomatch hm1
                      | cons hd tl ih =>
                        obtain ⟨hnot_l, hnd_tl⟩ := List.nodup_cons.mp hnd
                        rcases List.mem_cons.mp hm1 with rfl | hm1' <;>
                          rcases List.mem_cons.mp hm2 with h2 | hm2'
                        · exact (Prod.mk.inj (Prod.mk.inj h2).2).2
                        · exact False.elim (hnot_l (List.mem_map.mpr ⟨_, hm2', rfl⟩))
                        · subst h2; exact False.elim (hnot_l (List.mem_map.mpr ⟨_, hm1', rfl⟩))
                        · exact ih hnd_tl hm1' hm2'
                    have hklr_map_eq :
                        st.kyberLastResort.map (fun (i, k, s) =>
                          if i = m.kpkId then (i, k, s ++ [(m.spkId, m.baseKey)]) else (i, k, s)) =
                        st.kyberLastResort.map (fun (i, k, s) =>
                          if i = m.kpkId then (i, k, seen ++ [(m.spkId, m.baseKey)])
                          else (i, k, s)) := by
                      refine List.map_congr_left fun ⟨i, k, s⟩ hmem => ?_
                      dsimp only
                      by_cases hi : i = m.kpkId
                      · subst hi
                        rw [huniq_seen hnd_klr hm_klr hmem]
                      · simp only [hi, ↓reduceIte]
                    rw [hklr_map_eq] at heq7_fn ⊢
                    obtain ⟨hbk_str, hbk_asc⟩ := DecPkS0.baseKeys_path_eq m.kpkId
                    have hw := DecPkS0.namedWrites_of_dirs st.party.other
                      (⟨⟨m.idPub⟩⟩ : IdentityKey).serialize
                      (d2cRecordBytes_placed x' x₀ gs g₀)
                      StoresGhost.opened.kyber.oneTime
                      (StoresGhost.opened.kyber.lastResort.put (baseKeysName m.kpkId)
                        (baseKeysBytes (seen ++ [(m.spkId, m.baseKey)])))
                      otDir
                      (w8 := [])
                      (w9 := [(baseKeysFile m.kpkId, baseKeysBytes (seen ++ [(m.spkId, m.baseKey)]))])
                      (w7 := w7)
                      ⟨fun _ h => False.elim (List.not_mem_nil h), rfl⟩
                      ⟨fun pw hpw bt hbt => by
                         change pw ∈ ((DirGhost.new _).put _ _).writes at hpw
                         rw [DecPkS0.new_put_writes, List.mem_singleton] at hpw
                         subst hpw; exact hbk_asc bt hbt,
                       by change ((DirGhost.new _).put _ _).writes.map _ = _
                          rw [DecPkS0.new_put_writes, List.map_cons, List.map_nil, hbk_str]⟩
                      hot_wr
                    rw [hw]
                    have hparty_eq : ∀ q,
                        (DecPkS0.blockDir7 W st ++ w7).reverse.find? (fun u => u.1 == q) =
                          (DecPkS0.blockDir7 W st ++ DecPkS0.blockDir7 W
                            { removeOpk
                                { st with kyberLastResort := st.kyberLastResort.map (fun (i, k, s) =>
                                    if i = m.kpkId then (i, k, seen ++ [(m.spkId, m.baseKey)])
                                    else (i, k, s)) } m with
                              peerId := some ⟨⟨m.idPub⟩⟩, session := some (x', gs) }).reverse.find?
                            (fun u => u.1 == q) := by
                      intro q
                      have hsame_ot :
                          (removeOpk
                            { st with kyberLastResort := st.kyberLastResort.map (fun (i, k, s) =>
                                if i = m.kpkId then (i, k, seen ++ [(m.spkId, m.baseKey)])
                                else (i, k, s)) } m).oneTime =
                          (removeOpk st m).oneTime := by
                        unfold removeOpk; cases m.opkId <;> rfl
                      exact heq7_fn hsame_ot rfl q
                    have h8_rem : ∀ st0 : PqParty,
                        (removeOpk st0 m).kyberOneTime = st0.kyberOneTime := by
                      intro st0; unfold removeOpk; cases m.opkId <;> rfl
                    have h9_rem : ∀ st0 : PqParty,
                        (removeOpk st0 m).kyberLastResort = st0.kyberLastResort := by
                      intro st0; unfold removeOpk; cases m.opkId <;> rfl
                    have h1_rem : ∀ st0 : PqParty, (removeOpk st0 m).party = st0.party := by
                      intro st0; unfold removeOpk; cases m.opkId <;> rfl
                    have h2_rem : ∀ st0 : PqParty, (removeOpk st0 m).me = st0.me := by
                      intro st0; unfold removeOpk; cases m.opkId <;> rfl
                    have h6_rem : ∀ st0 : PqParty, (removeOpk st0 m).signed = st0.signed := by
                      intro st0; unfold removeOpk; cases m.opkId <;> rfl
                    exact filesOf_commit_master_d2c_placed W st _ (wirePrekey :: m.bytes) rc _ rfl rfl
                      (fun _ h => by
                        rw [List.mem_singleton] at h; subst h
                        exact DecPkS0.recvBucket_identityFile _)
                      hb7
                      (fun _ h => False.elim (List.not_mem_nil h))
                      (fun _ h => by
                        rw [List.mem_singleton] at h; subst h
                        exact DecPkS0.recvBucket_baseKeysFile _)
                      hw7
                      (fun _ h => False.elim (List.not_mem_nil h))
                      (fun _ h => by
                        rw [List.mem_singleton] at h; subst h
                        exact DecPkS0.isRecvFile_baseKeysFile _)
                      (by simp only [h1_rem])
                      (by simp only [DecPkS0.blockDir2, h2_rem])
                      (by simp only [DecPkS0.blockDir3, h2_rem])
                      (by simp only [DecPkS0.blockDir4, h1_rem])
                      (by simp only [DecPkS0.blockDir6, h6_rem])
                      hparty_eq
                      (fun q => by
                        have h8' : DecPkS0.blockDir8
                            { removeOpk
                                { st with kyberLastResort := st.kyberLastResort.map (fun (i, k, s) =>
                                    if i = m.kpkId then (i, k, seen ++ [(m.spkId, m.baseKey)])
                                    else (i, k, s)) } m with
                              peerId := some ⟨⟨m.idPub⟩⟩, session := some (x', gs) } =
                            DecPkS0.blockDir8 st := by
                          simp only [DecPkS0.blockDir8, h8_rem]
                        rw [h8', List.append_nil]
                        exact DecPkS0.find?_self_double _ q)
                      (fun q => by
                        have h9' : DecPkS0.blockDir9
                            { removeOpk
                                { st with kyberLastResort := st.kyberLastResort.map (fun (i, k, s) =>
                                    if i = m.kpkId then (i, k, seen ++ [(m.spkId, m.baseKey)])
                                    else (i, k, s)) } m with
                              peerId := some ⟨⟨m.idPub⟩⟩, session := some (x', gs) } =
                            (((st.kyberLastResort.map (fun (i, k, s) =>
                              if i = m.kpkId then (i, k, seen ++ [(m.spkId, m.baseKey)])
                              else (i, k, s))).map
                              (fun (i, k, s) =>
                              [(lastResortKyberPreKeyFile i, kyberRecordBytes i k),
                               (baseKeysFile i, baseKeysBytes s)])).flatten) := by
                          simp only [DecPkS0.blockDir9, h9_rem]
                        rw [h9']
                        exact DecPkS0.find?_lr_update hm_klr q)

/-! ### Deriving `ObservedExceptNormPlaced` and Session-File Divergence from `d2cObserve_placed` -/

private def HasParentDirsLocal (fs : FsState) : Prop :=
  ∀ d ∈ DecPkS0.recvParentDirs, fs.entries [d] = some .dir

private theorem hasParentDirs_partyDirs_local :
    HasParentDirsLocal (dirsFold partyDirs {}) := by
  unfold HasParentDirsLocal
  intro d hd
  revert d hd
  decide

private theorem filesFold_step_isRecvFile_local {fs : FsState} (hdirs : HasParentDirsLocal fs)
    {p : String} (bs : List (BitVec 8)) (hp : DecPkS0.IsRecvFile p) :
    let fs' := (((FsPath.nonEmptyPrefixes (normalizePath p)).dropLast).foldl
      (fun acc pref => acc.setEntry pref (some .dir)) fs).setFile p (some (.file bs))
    HasParentDirsLocal fs' ∧
      ∀ k : FsPath, fs'.entries k =
        if k == normalizePath p then some (.file bs) else fs.entries k := by
  intro fs'
  have hpoint : ∀ k : FsPath, fs'.entries k =
      if k == normalizePath p then some (.file bs) else fs.entries k := by
    intro k
    rcases DecPkS0.isRecvFile_norm_shape hp with ⟨_, hn⟩ | ⟨d0, sfx, hd0, _, hn⟩
    · simp only [fs', FsState.setFile, hn, FsPath.nonEmptyPrefixes, List.map_nil,
        List.dropLast, List.foldl_nil, FsState.setEntry]
    · simp only [fs', FsState.setFile, hn, FsPath.nonEmptyPrefixes, List.map_cons,
        List.map_nil, List.dropLast, List.foldl_cons, List.foldl_nil, FsState.setEntry]
      cases hk2 : (k == [d0, sfx]) with
      | true => rfl
      | false =>
        cases hk1 : (k == [d0]) with
        | false => rfl
        | true =>
          rw [beq_iff_eq.mp hk1, hdirs d0 hd0]
          rfl
  refine ⟨fun d hd => ?_, hpoint⟩
  rw [hpoint [d]]
  rcases DecPkS0.isRecvFile_norm_shape hp with ⟨hr, hn⟩ | ⟨d0, sfx, _, _, hn⟩
  · have hne : ([d] == [p]) = false :=
      beq_false_of_ne (fun e => (DecPkS0.recvRootFiles_props hr).2.1 (List.singleton_injective e ▸ hd))
    rw [hn, hne]
    exact hdirs d hd
  · have hne : ([d] == [d0, sfx]) = false := beq_false_of_ne (by simp)
    rw [hn, hne]
    exact hdirs d hd

private theorem filesFold_isRecvFile_entries_local {L : List (String × List (BitVec 8))}
    (hL : ∀ x ∈ L, DecPkS0.IsRecvFile x.1) {fs : FsState} (hdirs : HasParentDirsLocal fs) :
    HasParentDirsLocal (filesFold L fs) ∧
      ∀ k : FsPath, (filesFold L fs).entries k =
        match L.reverse.find? (fun x => normalizePath x.1 == k) with
        | some pb => some (FsEntry.file pb.2)
        | none => fs.entries k := by
  induction L generalizing fs with
  | nil => exact ⟨hdirs, fun _ => rfl⟩
  | cons hd tl ih =>
    rcases hd with ⟨p, bs⟩
    obtain ⟨hstep_dirs, hstep_eq⟩ :=
      filesFold_step_isRecvFile_local hdirs bs (hL (p, bs) List.mem_cons_self)
    unfold filesFold
    rw [List.foldl_cons]
    change HasParentDirsLocal (filesFold tl _) ∧ ∀ k, (filesFold tl _).entries k = _
    obtain ⟨hfinal_dirs, hfinal_eq⟩ :=
      ih (fun x hx => hL x (List.mem_cons_of_mem _ hx)) hstep_dirs
    refine ⟨hfinal_dirs, fun k => ?_⟩
    rw [hfinal_eq k, List.reverse_cons, List.find?_append]
    cases tl.reverse.find? (fun x => normalizePath x.1 == k) with
    | some pb => rfl
    | none =>
      simp only [Option.none_or, List.find?_singleton, hstep_eq k]
      have hsymm : (normalizePath p == k) = (k == normalizePath p) := by
        cases h1 : (normalizePath p == k) <;> cases h2 : (k == normalizePath p)
        · rfl
        · exact absurd (beq_iff_eq.mp h2).symm (beq_eq_false_iff_ne.mp h1)
        · exact absurd (beq_iff_eq.mp h1).symm (beq_eq_false_iff_ne.mp h2)
        · rfl
      rw [hsymm]
      cases (k == normalizePath p) <;> rfl

theorem filesOf_append_singleton_ne_norm_placed {L : List (String × List (BitVec 8))}
    (hL : ∀ x ∈ L, DecPkS0.IsRecvFile x.1) {p : String} (hp : DecPkS0.IsRecvFile p)
    (bs : List (BitVec 8)) {q : String}
    (hq : Arm64.normalizePath q ≠ Arm64.normalizePath p) :
    filesOf (L ++ [(p, bs)]) q = filesOf L q := by
  have hLp : ∀ x ∈ L ++ [(p, bs)], DecPkS0.IsRecvFile x.1 := by
    intro x hx
    rcases List.mem_append.mp hx with h1 | h2
    · exact hL x h1
    · rw [List.mem_singleton] at h2; subst h2; exact hp
  have heq1 := congrFun (fsView_initFsState { dirs := partyDirs, files := L ++ [(p, bs)] }).symm q
  have heq2 := congrFun (fsView_initFsState { dirs := partyDirs, files := L }).symm q
  rw [heq1, heq2]
  unfold fsView
  split
  · rfl
  · next hstdio =>
    show fileOfEntry
        ((Process.initFsState { dirs := partyDirs, files := L ++ [(p, bs)] }).files q) =
      fileOfEntry
        ((Process.initFsState { dirs := partyDirs, files := L }).files q)
    simp only [FsState.files, FsState.getEntry]
    split
    · rfl
    · rw [initFsState_entries { dirs := partyDirs, files := L ++ [(p, bs)] }
          (normalizePath q) hstdio,
        initFsState_entries { dirs := partyDirs, files := L }
          (normalizePath q) hstdio]
      dsimp only
      rw [(filesFold_isRecvFile_entries_local hLp hasParentDirs_partyDirs_local).2
          (normalizePath q),
        (filesFold_isRecvFile_entries_local hL hasParentDirs_partyDirs_local).2
          (normalizePath q)]
      have hne_beq : (normalizePath p == normalizePath q) = false :=
        beq_false_of_ne (Ne.symm hq)
      simp only [List.reverse_append, List.reverse_singleton, List.find?_append,
        List.find?_singleton, hne_beq, Bool.false_eq_true, ↓reduceIte, Option.none_or]

/-- `d2cObserve_placed` on `pqRecvInputs` satisfies `ObservedExceptNormPlaced` against `pqxdhExpectedOutcome` at
`sessionFile (partyAddress peer)`. -/
theorem d2cObserve_agreeExceptNorm_placed (W : PEParams) (st : PqParty) (c : List (BitVec 8))
    (rc : BitVec 256) (peer : Party) (x₀ : RecordExtras) (g₀ : GhostState E2E.Bytes)
    (r : Option (Option (PqParty × List (BitVec 8)))) :
    ObservedExceptNormPlaced W (pqRecvInputs W st c rc) (sessionFile (partyAddress peer)) r
      (d2cObserve_placed W (pqRecvInputs W st c rc) peer x₀ g₀ r) := by
  cases r with
  | none => rfl
  | some o =>
    cases o with
    | none => rfl
    | some pair =>
      rcases pair with ⟨st', out⟩
      refine ⟨rfl, rfl, fun q hq => ?_⟩
      cases st'.session with
      | none =>
        simp only [List.append_nil]
      | some xg =>
        rcases xg with ⟨x', gs⟩
        exact filesOf_append_singleton_ne_norm_placed
          (fun x hx => by
            rcases List.mem_append.mp hx with h1 | h2
            · exact DecPkS0.isRecvFile_pqRecv_files W st c rc x h1
            · exact DecPkS0.isRecvFile_encodeDir W st' x h2)
          (DecPkS0.isRecvFile_sessionFile peer)
          (d2cRecordBytes_placed x' x₀ gs g₀) hq

/-- `ObservedExceptNormPlaced` for D2(c) `NoMatch` runs. -/
theorem runAns_pqRecvPrekey_noMatch_exceptNorm_placed (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hS : S.decryptPrekey = decPkDefD2c X W Scope)
    (hP : RunRefine.PksmParseAgrees S)
    (hpksm : PksmTyped S)
    (hinj : Slots.EncodeInjOn Scope) (hcov : ScopeCoversPq W Scope)
    (st : PqParty) (x₀ : RecordExtras) (g₀ : GhostState E2E.Bytes)
    (m : PreKeyMessageFields) (rc : BitVec 256)
    (hwf : PqxdhPartyInSpecDomain W st) (hs : st.session = some (x₀, g₀))
    (hm : m.inner.length + 2048 < 2 ^ 32)
    (hnot : ¬ PqSessionMatches x₀ g₀ m) :
    ObservedExceptNormPlaced W (pqRecvInputs W st (wirePrekey :: m.bytes) rc)
      (sessionFile (partyAddress st.party.other))
      (pqRecvPrekeyModel X W { st with session := none } m rc)
      (observe (pqRecvInputs W st (wirePrekey :: m.bytes) rc).files
        (runAns S (pqRecvInputs W st (wirePrekey :: m.bytes) rc))) := by
  rw [runAns_pqRecvPrekey_noMatch_exact_placed S X W Scope hS hP hpksm hinj hcov st x₀ g₀ m rc
    hwf hs hm hnot]
  exact d2cObserve_agreeExceptNorm_placed W st (wirePrekey :: m.bytes) rc st.party.other x₀ g₀ _

/-- Evaluates `filesOf L (sessionFile (partyAddress P))` for any `IsRecvFile` list `L`. -/
theorem filesOf_eval_isRecvFile_sessionFile_placed {L : List (String × List (BitVec 8))}
    (hL : ∀ x ∈ L, DecPkS0.IsRecvFile x.1) (P : Party) :
    filesOf L (sessionFile (partyAddress P)) =
      (L.reverse.find? (fun x => x.1 == sessionFile (partyAddress P))).map Prod.snd := by
  let p := sessionFile (partyAddress P)
  have hp_rf : DecPkS0.IsRecvFile p := DecPkS0.isRecvFile_sessionFile P
  have heq := congrFun (fsView_initFsState { dirs := partyDirs, files := L }).symm p
  rw [heq]
  unfold fsView
  split
  · next hstd => cases P <;> exact absurd hstd (by decide)
  · next hstd =>
    show fileOfEntry ((Process.initFsState { dirs := partyDirs, files := L }).files p) = _
    simp only [FsState.files, FsState.getEntry]
    split
    · next hnil => cases P <;> exact absurd hnil (by decide)
    · rw [initFsState_entries { dirs := partyDirs, files := L } (normalizePath p) hstd]
      dsimp only
      rw [(filesFold_isRecvFile_entries_local hL hasParentDirs_partyDirs_local).2
          (normalizePath p)]
      have hnf : fileOfEntry ((dirsFold partyDirs {}).entries (normalizePath p)) = none :=
        NoFiles.dirsFold_none partyDirs (normalizePath p)
      have aux : ∀ l : List (String × List (BitVec 8)), (∀ x ∈ l, DecPkS0.IsRecvFile x.1) →
          l.find? (fun x => normalizePath x.1 == normalizePath p) =
          l.find? (fun x => x.1 == p) := by
        intro l hl
        induction l with
        | nil => rfl
        | cons hd tl ih =>
          have hhd := hl hd List.mem_cons_self
          have hb : (normalizePath hd.1 == normalizePath p) = (hd.1 == p) := by
            cases b1 : (normalizePath hd.1 == normalizePath p) <;> cases b2 : (hd.1 == p)
            · rfl
            · exact absurd (congrArg normalizePath (beq_iff_eq.mp b2)) (beq_eq_false_iff_ne.mp b1)
            · exact absurd (DecPkS0.isRecvFile_norm_inj hhd hp_rf (beq_iff_eq.mp b1))
                (beq_eq_false_iff_ne.mp b2)
            · rfl
          simp only [List.find?_cons, hb, ih (fun x hx => hl x (List.mem_cons_of_mem _ hx))]
      rw [aux L.reverse (fun x hx => hL x (List.mem_reverse.mp hx))]
      cases L.reverse.find? (fun x => x.1 == p) with
      | some _ => rfl
      | none => exact hnf

/-- On an accepting post-state `st'` (`st'.party = st.party`, `st'.session = some (x', gs)`),
`d2cObserve_placed` stores `some (d2cRecordBytes_placed x' x₀ gs g₀)` at `sessionFile (partyAddress st.party.other)`
whereas `pqxdhExpectedOutcome` stores `some (encodeRecordUnderExtras (fun _ => x') gs)`. -/
theorem filesOf_d2c_and_pq_at_sessionFile_placed (W : PEParams) (st st' : PqParty)
    (c : List (BitVec 8)) (rc : BitVec 256)
    (x' x₀ : RecordExtras) (gs g₀ : GhostState E2E.Bytes)
    (hparty : st'.party = st.party) (hsess : st'.session = some (x', gs)) :
    let p := sessionFile (partyAddress st.party.other)
    let L := (pqRecvInputs W st c rc).files ++ encodeDir W st'
    filesOf (L ++ [(p, d2cRecordBytes_placed x' x₀ gs g₀)]) p = some (d2cRecordBytes_placed x' x₀ gs g₀) ∧
      filesOf L p = some (encodeRecordUnderExtras (fun _ => x') gs) := by
  dsimp only
  let p := sessionFile (partyAddress st.party.other)
  let L := (pqRecvInputs W st c rc).files ++ encodeDir W st'
  have hL : ∀ x ∈ L, DecPkS0.IsRecvFile x.1 := by
    intro x hx
    rcases List.mem_append.mp hx with h1 | h2
    · exact DecPkS0.isRecvFile_pqRecv_files W st c rc x h1
    · exact DecPkS0.isRecvFile_encodeDir W st' x h2
  have hLp : ∀ x ∈ L ++ [(p, d2cRecordBytes_placed x' x₀ gs g₀)], DecPkS0.IsRecvFile x.1 := by
    intro x hx
    rcases List.mem_append.mp hx with h1 | h2
    · exact hL x h1
    · rw [List.mem_singleton] at h2; subst h2
      exact DecPkS0.isRecvFile_sessionFile st.party.other
  rw [filesOf_eval_isRecvFile_sessionFile_placed hLp st.party.other,
    filesOf_eval_isRecvFile_sessionFile_placed hL st.party.other]
  refine ⟨?_, ?_⟩
  · simp [p]
  · obtain ⟨d1', d2', d3', d4', d5', d6', d7', d8', d9'⟩ := DecPkS0.bucket_blockDir W st'
    have hb5 : DecPkS0.recvBucket p = 5 := DecPkS0.recvBucket_sessionFile _
    simp only [L, List.reverse_append, List.find?_append]
    rw [DecPkS0.encodeDir_blocks W st',
      DecPkS0.find?_select_block d1' d2' d3' d4' d5' d6' d7' d8' d9' p, hb5]
    unfold DecPkS0.blockDir5
    rw [hparty, hsess]
    simp [p]

/-- Every accepting answer of `pqRecvPrekeyModel X W { st with session := none } m rc` preserves
`party` and installs a `some (x', gs)` session. -/
theorem pqRecvPrekeyModel_none_accept_shape_placed (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (st : PqParty) (m : PreKeyMessageFields) (rc : BitVec 256)
    {st' : PqParty} {out : List (BitVec 8)}
    (h : pqRecvPrekeyModel X W { st with session := none } m rc = some (some (st', out))) :
    ∃ x' gs, st'.party = st.party ∧ st'.session = some (x', gs) := by
  unfold pqRecvPrekeyModel at h
  cases htf : SignalMessage.tryFrom protoSignalCodec m.inner with
  | error _ => rw [htf] at h; cases h
  | ok inner =>
    rw [htf] at h
    dsimp only at h
    split at h
    · cases h
    · cases hk : preKeysNamedBy { st with session := none } m with
      | none => rw [hk] at h; cases h
      | some k =>
        rw [hk] at h
        dsimp only at h
        cases hr : recvPrekeyState X W st.party st.me k m rc with
        | none => rw [hr] at h; cases h
        | some o =>
          rw [hr] at h
          cases o with
          | none => cases h
          | some triple =>
            rcases triple with ⟨x', gs, pt⟩
            dsimp only at h
            cases hmk : markKyberUsed { st with session := none } m with
            | none => rw [hmk] at h; cases h
            | some st1 =>
              rw [hmk] at h
              dsimp only at h
              injection h with h1
              injection h1 with h2
              obtain ⟨rfl, _⟩ := Prod.mk.inj h2
              have hp1 : st1.party = st.party := by
                unfold markKyberUsed at hmk
                dsimp only at hmk
                cases hl1 : List.lookup m.kpkId st.kyberOneTime with
                | none =>
                  rw [hl1] at hmk
                  dsimp only at hmk
                  cases hl2 : List.lookup m.kpkId st.kyberLastResort with
                  | none => rw [hl2] at hmk; cases hmk
                  | some ks =>
                    rcases ks with ⟨_, seen⟩
                    rw [hl2] at hmk
                    dsimp only at hmk
                    split at hmk
                    · cases hmk
                    · injection hmk with hst1; subst hst1; rfl
                | some ov =>
                  rw [hl1] at hmk
                  cases ov with
                  | none =>
                    dsimp only at hmk
                    cases hl2 : List.lookup m.kpkId st.kyberLastResort with
                    | none => rw [hl2] at hmk; cases hmk
                    | some ks =>
                      rcases ks with ⟨_, seen⟩
                      rw [hl2] at hmk
                      dsimp only at hmk
                      split at hmk
                      · cases hmk
                      · injection hmk with hst1; subst hst1; rfl
                  | some _ =>
                    dsimp only at hmk
                    injection hmk with hst1; subst hst1; rfl
              have hrem : (removeOpk st1 m).party = st1.party := by
                unfold removeOpk
                cases m.opkId <;> rfl
              exact ⟨x', gs, hrem.trans hp1, rfl⟩

end CryptoVerification.SignalSession.Cli.RunProofs

namespace CryptoVerification.SignalSession.Cli.RunCompose

open Arm64 Arm64.Obj ProofLib
open CryptoVerification.E2E
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalPublicApi
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.Main.Placed
open CryptoVerification.SignalSession.Cli.Run.Placed
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunProofs
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (CliGhostHooks cliGhostExterns)

theorem cliDecryptPrekeyNeed_le : cliDecryptPrekeyNeed cliRunBudgets_placed ≤ 4194304 := by decide

/-- `signal_session::run` meets `runSpecTightPlaced` at `cliRunSem_placed` with `decPkDefD2c` and
`DecPkOkD2c`, given `DecPkD2cSlotOkPlaced mmpl g W` and `PksmSlotOkPlaced mmpl g W`. -/
theorem hrun_cli_d2c_tight_placed [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (hpub : CliPubCalleesPlaced mmpl g W)
    (hslots : CliSlotCalleesPlaced mmpl g X W)
    (hslot : DecPkD2cSlotOkPlaced mmpl g W)
    (hpksm : PksmSlotOkPlaced mmpl g W) :
    subroutine_ok (mProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 579)
      (runSpecTightPlaced (LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl)
        E2E.HooksE.A0 uuidTryParse
        (runRel (cliRunSem_placed X W (decPkDefD2c X ⟨W.C, W.Q⟩ Slots.scopeIn)
          (DecPkOkD2c ⟨W.C, W.Q⟩ Slots.scopeIn) Pksm.pksmParse))
        cliWrOk cliResStack) :=
  hrun_cli_placed mmpl g X W
    (decPkDefD2c X ⟨W.C, W.Q⟩ Slots.scopeIn)
    (DecPkOkD2c ⟨W.C, W.Q⟩ Slots.scopeIn)
    Pksm.pksmParse
    (cliDecryptPrekeyNeed cliRunBudgets_placed)
    cliDecryptPrekeyNeed_le
    hpub
    hslots
    (hslot X _ (cliRunNeeds_placed (cliDecryptPrekeyNeed cliRunBudgets_placed)) rfl rfl rfl rfl)
    (hpksm _ rfl)

/-- `signal_session::run` meets `runSpecPlaced` at `cliRunSem_placed` with `decPkDefD2c` and
`DecPkOkD2c`, given `DecPkD2cSlotOkPlaced mmpl g W` and `PksmSlotOkPlaced mmpl g W`. -/
theorem hrun_cli_d2c_placed [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (hpub : CliPubCalleesPlaced mmpl g W)
    (hslots : CliSlotCalleesPlaced mmpl g X W)
    (hslot : DecPkD2cSlotOkPlaced mmpl g W)
    (hpksm : PksmSlotOkPlaced mmpl g W) :
    subroutine_ok (mProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 579)
      (runSpecPlaced (LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl)
        E2E.HooksE.A0 uuidTryParse
        (runRel (cliRunSem_placed X W (decPkDefD2c X ⟨W.C, W.Q⟩ Slots.scopeIn)
          (DecPkOkD2c ⟨W.C, W.Q⟩ Slots.scopeIn) Pksm.pksmParse))
        cliWrOk cliResStack) :=
  subroutine_ok_runSpecPlaced_of_tight
    (hrun_cli_d2c_tight_placed mmpl g X W hpub hslots hslot hpksm)

end CryptoVerification.SignalSession.Cli.RunCompose
