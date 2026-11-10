/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Cli.Slots.RecvWhisperDefs
public import Symbolic.Proofs.Swarm.CREF.TR.RecvDecStepPure
import Symbolic.Proofs.RngG.R3Canon
import Symbolic.Proofs.Swarm.CREF.Cli.Slots.RecvWhisperCodec
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.SessionPrimsPure -- shake: keep

/-!
# Whisper Receive Accept Evaluation Bridge

Connects an accepting `pqRecvWhisperModel` step under `WhisperSlotPre` to `pqRecvWhisperMid`,
`CoinSplit` over `cliOutcomeEvents`, `pureEvalRecvWireWithCoinsW`, and post-state `WireRecCanon`
and `TRRecordCanon` (`pqRecvWhisper_accept_eval`).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.Cli.Slots
open Symbolic.Swarm.CREF.CliPure hiding pureDrawsCoins
open Symbolic.Swarm.CREF.CliPureRcv

cref_open
open Symbolic.Swarm.CREF.CliPure hiding pureDrawsCoins
open Symbolic.Swarm.CREF.CliPureRcv
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (MachineEvent)
open DY.Libsignal.Rust (RecordRec)
open DY.Libsignal.Composed.Refinement
open DY.Libsignal.Composed.Refinement.Cli
  (CliCall CoinSplit cliEntryEvents cliExitEvents)
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E CryptoVerification.E2E.InMem CryptoVerification.E2E.RecordX
open CryptoVerification.E2E.Bin
  (Role evalOpen storedSession inMemAnswers)
open CryptoVerification.E2E.Pqxdh.WireEntries.SymP3 (RecvWireGhost)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.SignalSession
open Proofs.libsignal.Hooks2 (cryptoOf')
open Proofs.libsignal.SR (AesW interpW messageDecryptSignalW)
open Symbolic.Swarm.CREF.TR.Pure (slots_RecordCanonical_Q slots_NonEmptyV1Q slots_DeserializeScopeP_Q slots_RecordScopeP slots_RecordInScopeP PureBinCanonSession WireRecCanon TRRecordCanon)
open Symbolic.Swarm.CREF.CliPure.TR.PureRecvEval (pureCoinsOf pureSerializeRole pureDrawsCoins tryDecryptFromRecordW_coins_irrel_of_pureDrawsCoins_false pureEvalRecvWireWithCoinsW trRecordCanon_of_pureWireRecCanon_pqInj)
open Symbolic.Swarm.TRREF.GrowthRecordPure
  (pureSpqr drCaps_of_pureBinCanonSession pq_length_le_encodeRecord_pure
   encodeRecord_storedSession_decryptW_lt_pure spqrOooBounded_storedSession_decryptW_pure)
open Symbolic.Swarm.TRREF.SpqrSemOf (spqrModelOf)
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPureRcv
open Symbolic.Swarm.CREF.CliPure hiding pureDrawsCoins
open Symbolic.Swarm.CREF.Cli

private theorem flatMap_blockToBytesLE_length_rwe (cs : List CBC.Block) :
    (cs.flatMap CBC.blockToBytesLE).length = 16 * cs.length := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.flatMap_cons, List.length_append, ih, List.length_cons, CBC.blockToBytesLE,
      List.length_ofFn]
    omega

private theorem cbcDecryptBlocks_length_rwe (g : CBC.Block → CBC.Block) (prev : CBC.Block)
    (cs : List CBC.Block) :
    (CBC.cbcDecryptBlocks g prev cs).length = cs.length := by
  induction cs generalizing prev with
  | nil => rfl
  | cons c cs ih => simp [CBC.cbcDecryptBlocks, ih]

private theorem pkcs7Unpad_length_le_rwe {bs pt : List (BitVec 8)}
    (h : CBC.pkcs7Unpad bs = some pt) :
    pt.length ≤ bs.length := by
  unfold CBC.pkcs7Unpad at h
  split at h
  · contradiction
  · dsimp only at h
    split at h
    · contradiction
    · split at h
      · simp only [Option.some.injEq] at h
        subst h
        simp only [List.length_take]
        omega
      · contradiction

private theorem aesCbcDecrypt_length_le_rwe {D : CBC.AesKey → CBC.Block → CBC.Block}
    {k : CBC.AesKey} {iv : CBC.Block} {ct pt : List (BitVec 8)}
    (hdec : aesCbcDecrypt D k iv ct = some pt) :
    pt.length ≤ ct.length := by
  unfold aesCbcDecrypt CBC.cbcDecRaw at hdec
  split at hdec
  · simp at hdec
  · have hle := pkcs7Unpad_length_le_rwe hdec
    rw [flatMap_blockToBytesLE_length_rwe, cbcDecryptBlocks_length_rwe, CBC.chunks16,
      List.length_ofFn] at hle
    omega

private theorem tryDecryptFromRecord_pt_length_le {PQ PQC : Type} [Inhabited PQ]
    (C : Crypto) (spqr : Spqr PQ PQC) (expected : Option (List (BitVec 8)))
    (msg : SignalMessage) (msgType : MessageType) (coins : BitVec 256)
    (st st' : SessionState PQ) (pt : List (BitVec 8))
    (h : SessionState.tryDecryptFromRecord C spqr expected msg msgType coins st = (.ok pt, st')) :
    pt.length ≤ msg.ciphertext.length := by
  have hW : Proofs.libsignal.SR.SessionState.tryDecryptFromRecordW C
      (Proofs.libsignal.SR.cbcW C) spqr expected msg msgType coins st = (.ok pt, st') := h
  obtain ⟨_, _, _, _, _, _, _, _, hDec, _, _⟩ :=
    Proofs.libsignal.RngG.R3.decryptW_ok_branch hW
  exact aesCbcDecrypt_length_le_rwe hDec

abbrev recvWireMissFactPure :=
  Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepPure.recvWireMissFact

/-- Hardware RNG event list emitted inside an accepting whisper `recv` call (`[.rng coins]` when
`pureDrawsCoins` holds, and `[]` otherwise). -/
noncomputable def pqRecvWhisperMid (interp : ExternInterpretation) (st : PqParty)
    (body coins : HwBytes) : List MachineEvent :=
  match st.session, SignalMessage.tryFrom protoSignalCodec body with
  | some (x, g_sess), .ok msg =>
    if pureDrawsCoins (cryptoOf' interp) (pqSession x g_sess).state msg.senderRatchetKey then
      [.rng coins]
    else []
  | _, _ => []

theorem coinSplit_recvWhisper_accept_mid {c : CliCall} {peer : Address}
    (interp : ExternInterpretation) (st : PqParty) (body pt : HwBytes)
    (hcmd : c.cmd = .recv peer) (hstdin : c.stdin = wireWhisperTag :: body)
    (hc_ne : c.coins ≠ []) :
    CoinSplit (cliEntryEvents c ++ cliExitEvents c 0 pt)
      (.recv (wireWhisperTag :: body) :: (pqRecvWhisperMid interp st body c.coins ++ [.accept pt])) := by
  rw [cliEntryEvents_recvWhisper hcmd hstdin, cliExitEvents_recvWhisper_zero hcmd pt]
  unfold pqRecvWhisperMid
  rcases st.session with _ | ⟨x, g_sess⟩
  · exact coinSplit_recv_drop_rng_accept (wireWhisperTag :: body) c.coins pt
  · rcases SignalMessage.tryFrom protoSignalCodec body with _ | msg
    · exact coinSplit_recv_drop_rng_accept (wireWhisperTag :: body) c.coins pt
    · dsimp only
      split_ifs
      · exact coinSplit_recv_full_rng_accept (wireWhisperTag :: body) c.coins pt hc_ne
      · exact coinSplit_recv_drop_rng_accept (wireWhisperTag :: body) c.coins pt

private def decryptFlatWPure {Addr PQ PQC E : Type} [Inhabited PQ] (C : Crypto) (W_aes : AesW)
    (spqr : Spqr PQ PQC) (ser : Addr → Addr → Option (List (BitVec 8)))
    (answers : StoreAnswers PQ E) (ciphertext : SignalMessage) (remote loc : Addr)
    (coins : BitVec 256) :
    Except (ApiError Addr E) (List (BitVec 8)) × List (StoreCall Addr PQ) :=
  let load := StoreCall.loadSession remote
  match answers.loadSession with
  | .error e => (.error (.store e), [load])
  | .ok none => (.error (.sessionNotFound remote "message_decrypt_signal"), [load])
  | .ok (some record) =>
    match Proofs.libsignal.SR.SessionRecord.tryDecryptFromRecordW C W_aes spqr (ser remote loc)
        ciphertext coins record with
    | .error e => (.error (ApiError.ofProtocol e), [load])
    | .ok (ptext, record') =>
      match record'.currentSession.bind (·.state.remoteIdentity) with
      | none => (.error .panic, [load])
      | some k =>
        let trust := StoreCall.isTrustedIdentity remote k .receiving
        match answers.isTrustedIdentity with
        | .error e => (.error (.store e), [load, trust])
        | .ok false => (.error (.untrustedIdentity remote), [load, trust])
        | .ok true =>
          let save := StoreCall.saveIdentity remote k
          match answers.saveIdentity with
          | .error e => (.error (.store e), [load, trust, save])
          | .ok _ =>
            let store := StoreCall.storeSession remote record'
            match answers.storeSession with
            | .error e => (.error (.store e), [load, trust, save, store])
            | .ok () => (.ok ptext, [load, trust, save, store])

local macro "api_simp_eval" " [" xs:Lean.Parser.Tactic.simpLemma,* "]"
    loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp [Api.run, storeCall, liftProtocol, modify, modifyGet,
      MonadStateOf.modifyGet, ExceptT.run, StateT.run, bind, ExceptT.bind, ExceptT.mk,
      ExceptT.lift, ExceptT.bindCont, StateT.bind, pure, ExceptT.pure, StateT.pure,
      StateT.modifyGet, throw, throwThe, MonadExceptOf.throw, Id.run, liftM, monadLift,
      MonadLift.monadLift, MonadLiftT.monadLift, StateT.lift, StateT.map, Functor.map, get, getThe,
      MonadStateOf.get, StateT.get, set, MonadStateOf.set, StateT.set, $xs,*] $(loc)?)

private theorem messageDecryptSignalW_eq_flatWPure {Addr PQ PQC E : Type} [Inhabited PQ]
    (C : Crypto) (W_aes : AesW) (spqr : Spqr PQ PQC)
    (ser : Addr → Addr → Option (List (BitVec 8)))
    (answers : StoreAnswers PQ E) (ciphertext : SignalMessage) (remote loc : Addr)
    (coins : BitVec 256) :
    messageDecryptSignalW C W_aes spqr ser answers ciphertext remote loc coins =
      decryptFlatWPure C W_aes spqr ser answers ciphertext remote loc coins := by
  rcases answers with ⟨l, t, s, st⟩
  simp only [messageDecryptSignalW, decryptFlatWPure]
  rcases l with el | _ | record
  · api_simp_eval []
  · api_simp_eval []
  · rcases hd : Proofs.libsignal.SR.SessionRecord.tryDecryptFromRecordW C W_aes spqr
        (ser remote loc) ciphertext coins record with ed | ⟨ptext, record'⟩
    · api_simp_eval [hd]
    · rcases record' with ⟨_ | session⟩
      · api_simp_eval [hd]
      · rcases hk : session.state.remoteIdentity with _ | k
        · api_simp_eval [hd, hk]
        · rcases t with et | _ | _ <;> rcases s with es | _ <;> rcases st with est | _ <;>
            api_simp_eval [hd, hk]

/-- Connects `pqRecvWhisperModel W st body rc = some (some (st', pt))` under `WhisperSlotPre` to
`pureEvalRecvWireWithCoinsW`, `WireRecCanon`, `TRRecordCanon`, `pqRecvWhisperMid`, and `CoinSplit`. -/
theorem pqRecvWhisper_accept_eval
    {interp : ExternInterpretation} {W : PEParams}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {who : List Participant} {ok : Nat → Bool}
    {j : Nat} {p : Participant} {st st' : PqParty} {pt : HwBytes}
    {records : Participant → Option HwBytes}
    {sent accepted : List HwBytes} {opkUsed : Bool}
    {acc_hw : List MachineEvent} {body : HwBytes} (rc : BitVec 256)
    (hpre : WhisperSlotPre interp W r S who ok j p st records sent accepted opkUsed acc_hw body)
    (hacc : pqRecvWhisperModel W st body rc = some (some (st', pt))) :
    ∃ (x : RecordExtras) (g_sess : GhostState HwBytes) (s' : SessionState HwBytes) (k : IdentityKey)
      (_msg : SignalMessage) (g_rw : RecvWireGhost)
      (mid : List MachineEvent) (coins_eff : BitVec 256),
      let rec_in := encodeRecordUnderExtras (fun _ => x) g_sess
      let rec_out := encodeRecordUnderExtras (fun _ => x) { g_sess with session := s' }
      st.session = some (x, g_sess) ∧
      st' = { st with peerId := some k, session := some (x, { g_sess with session := s' }) } ∧
      records p = some rec_in ∧
      rec_in ≠ [] ∧
      SingleSession rec_in ∧
      TRRecordCanonPend rec_in ∧
      (∃ rr : RecordRec, rec_in = recordBytes rr ∧ rr.current.sessionVersion = 4#32) ∧
      rec_in.length < 2 ^ 31 ∧
      rec_out.length < 2 ^ 32 ∧
      pt.length < 2 ^ 32 ∧
      WireRecCanon rec_out ∧
      (rec_out.length < 2 ^ 32 - 2 ^ 20 → TRRecordCanon r p rec_out) ∧
      mid = pqRecvWhisperMid interp st body (HMAC.keyToBytes32 rc) ∧
      (mid = [] ∨ mid = [.rng (HMAC.keyToBytes32 rc)]) ∧
      CoinSplit
        (cliOutcomeEvents (cliRecvWhisperCall p st body rc)
          (some (pqxdhExpectedOutcome W (pqRecvInputs W st (wireWhisper :: body) rc) (some (some (st', pt))))))
        (.recv (wireWhisperTag :: body) :: (mid ++ [.accept pt])) ∧
      g_rw.who = (if p = r.alice then 0 else 1) ∧
      g_rw.wireBytes = wireWhisperTag :: body ∧
      slots_RecordCanonical_Q slots_NonEmptyV1Q rec_in g_rw.sess ∧
      ((coins_eff = 0#256 ∧ mid = [] ∧
          recvWireMissFactPure (cryptoOf' interp) (interpW interp) (spqrModelOf interp) g_rw) ∨
        (∃ rngBytes : HwBytes,
          mid = [.rng rngBytes] ∧ rngBytes.length = 32 ∧
          coins_eff = Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepPure.purePinCoins (some rngBytes) ∧
          (∀ m0, SignalMessage.tryFrom protoSignalCodec body = .ok m0 →
            pureDrawsCoins (cryptoOf' interp) g_rw.sess.state m0.senderRatchetKey = true))) ∧
      (∀ m0, SignalMessage.tryFrom protoSignalCodec body = .ok m0 →
        Symbolic.Swarm.CREF.CliPure.TR.PureRecvEval.PureDecryptCoinsOk (cryptoOf' interp)
          g_rw.sess.state m0.senderRatchetKey coins_eff) ∧
      pureEvalRecvWireWithCoinsW (cryptoOf' interp) (interpW interp) (spqrModelOf interp)
        g_rw coins_eff = some (rec_out, pt) := by
  unfold pqRecvWhisperModel at hacc
  rcases hsess : st.session with _ | ⟨x, g_sess⟩
  · simp [hsess] at hacc
  rw [hsess] at hacc
  rcases htry : SignalMessage.tryFrom protoSignalCodec body with _ | msg
  · simp [htry] at hacc
  rw [htry] at hacc
  dsimp only at hacc
  unfold pqxdhSessionDecryptModel at hacc
  rcases hdec : SessionState.tryDecryptFromRecord W.C (pqxdhSpqrSession W)
      ((pqxdhSessionParams W).expectedAddrs g_sess.party) msg .whisper rc g_sess.session with ⟨e | pt0, s'⟩
  · cases e <;> simp [hdec] at hacc
  rw [hdec] at hacc
  dsimp only at hacc
  rcases hrem_s' : s'.remoteIdentity with _ | k
  · simp [hrem_s'] at hacc
  rw [hrem_s'] at hacc
  dsimp only at hacc
  split_ifs at hacc with hntrust
  · simp at hacc
  simp only [Option.some.injEq, Prod.mk.injEq] at hacc
  rcases hacc with ⟨hst', hpt0⟩
  subst pt0
  obtain ⟨hrec_p, hrec_ne, hss, hcanonP, hrec4, hrcq_sx, hlen31, hg_party⟩ :=
    trRecordCanonPend_of_slotPre hpre hsess
  let sx := pqSession x g_sess
  have hsx_state : sx.state = g_sess.session := rfl
  let who_bv : BitVec 32 := if p = r.alice then 0#32 else 1#32
  have hparty_eq : g_sess.party = (if p = r.alice then Party.A else Party.B) :=
    hg_party.trans hpre.partyTag
  let role : Role := Role.ofParty g_sess.party
  have hrole_who : Role.ofWho who_bv = some role := by
    by_cases hp : p = r.alice <;> simp [who_bv, role, hparty_eq, hp, Role.ofWho, Role.ofParty]
  have haddr_eq : pureSerializeRole role.peer role =
      (pqxdhSessionParams W).expectedAddrs g_sess.party :=
    serializeAddrVal_role_expectedAddrs_pq W g_sess.party
  have hspqr_def : pureSpqrOf interp = pureSpqr (spqrModelOf interp) := rfl
  have hdecW_rc : Proofs.libsignal.SR.SessionState.tryDecryptFromRecordW (cryptoOf' interp)
      (interpW interp) (pureSpqr (spqrModelOf interp))
      (pureSerializeRole role.peer role) msg .whisper rc sx.state = (.ok pt, s') := by
    rw [haddr_eq, hsx_state, ← hspqr_def,
      ← tryDecryptFromRecord_eq_tryDecryptFromRecordW_of_bridge hpre.bridge]
    exact hdec
  obtain ⟨_hLocEq, hRemEq, hPpkFalse, _, _, _, _, _⟩ :=
    Proofs.libsignal.RngG.R3.tryDecryptFromRecordW_ok_state_props hdecW_rc
  have hrem_sx : sx.state.remoteIdentity.isSome = true := by
    rw [← hRemEq, hrem_s']; rfl
  have hpt_lt : pt.length < 2 ^ 32 := by
    have hct_le : msg.ciphertext.length ≤ body.length :=
      tryFrom_protoSignalCodec_ciphertext_length_le htry
    have hpt_le_ct : pt.length ≤ msg.ciphertext.length :=
      tryDecryptFromRecord_pt_length_le W.C (pqxdhSpqrSession W)
        ((pqxdhSessionParams W).expectedAddrs g_sess.party) msg .whisper rc g_sess.session s' pt hdec
    have hbody_lt := hpre.bodyLen
    omega
  let g_rw : RecvWireGhost :=
    { who := who_bv
      aPtr := 1#64
      meBytes := []
      stateBytes := encodeRecordUnderExtras (fun _ => x) g_sess
      sess := sx
      wirePtr := 0#64
      wireBytes := wireWhisperTag :: body
      cur := 0#64
      rest := HMAC.keyToBytes32 rc
      tlsInit := none }
  have hwho_grw : g_rw.who = (if p = r.alice then 0 else 1) := by
    by_cases hp : p = r.alice <;> simp [g_rw, who_bv, hp]
  have hpost_for_coins : ∀ (coins_eff : BitVec 256),
      Proofs.libsignal.SR.SessionState.tryDecryptFromRecordW (cryptoOf' interp)
        (interpW interp) (pureSpqr (spqrModelOf interp))
        (pureSerializeRole role.peer role) msg .whisper coins_eff sx.state =
        (.ok pt, s') →
      let rec_out := encodeRecordUnderExtras (fun _ => x) { g_sess with session := s' }
      rec_out.length < 2 ^ 32 ∧
      WireRecCanon rec_out ∧
      (rec_out.length < 2 ^ 32 - 2 ^ 20 → TRRecordCanon r p rec_out) ∧
      pureEvalRecvWireWithCoinsW (cryptoOf' interp) (interpW interp) (spqrModelOf interp)
        g_rw coins_eff = some (rec_out, pt) := by
    intro coins_eff hdec_eff rec_out
    have hmd_eq : messageDecryptSignalW (cryptoOf' interp) (interpW interp)
        (pureSpqr (spqrModelOf interp)) pureSerializeRole (inMemAnswers sx) msg
        role.peer role coins_eff =
        (.ok pt,
          [.loadSession role.peer,
           .isTrustedIdentity role.peer k .receiving,
           .saveIdentity role.peer k,
           .storeSession role.peer
             { currentSession := some
                 { sx with state := s', pendingPreKey := none, pendingKyberPreKey := none } }]) := by
      rw [messageDecryptSignalW_eq_flatWPure]
      simp [decryptFlatWPure, inMemAnswers,
        Proofs.libsignal.SR.SessionRecord.tryDecryptFromRecordW, hdec_eff, hrem_s']
    have hok1 : (messageDecryptSignalW (cryptoOf' interp) (interpW interp)
        (pureSpqr (spqrModelOf interp)) pureSerializeRole (inMemAnswers sx) msg
        role.peer role coins_eff).1 = .ok pt := by
      rw [hmd_eq]
    have hstored_eq : storedSession sx
        (messageDecryptSignalW (cryptoOf' interp) (interpW interp)
          (pureSpqr (spqrModelOf interp)) pureSerializeRole (inMemAnswers sx) msg
          role.peer role coins_eff).2 =
        { sx with state := s', pendingPreKey := none, pendingKyberPreKey := none } := by
      rw [hmd_eq]; rfl
    have hrec_out_eq : rec_out = CryptoVerification.E2E.Record.encodeRecord
        ⟨some (storedSession sx
          (messageDecryptSignalW (cryptoOf' interp) (interpW interp)
            (pureSpqr (spqrModelOf interp)) pureSerializeRole (inMemAnswers sx) msg
            role.peer role coins_eff).2)⟩ := by
      rw [hstored_eq]
      exact encodeRecordX_clearPending_eq_storedSession x g_sess s' hPpkFalse
    obtain ⟨hooo_in, hpqlen_in⟩ := ooo_of_trRecordCanonPend hcanonP hrcq_sx
    have hdrcaps_sx : Symbolic.Swarm.TRREF.GrowthRecord.DRCaps sx :=
      drCaps_of_pureBinCanonSession hrcq_sx.2.2
    have henc_sx_lt : (CryptoVerification.E2E.Record.encodeRecord ⟨some sx⟩).length <
        2 ^ 32 - 2 ^ 20 := by
      have heq : encodeRecordUnderExtras (fun _ => x) g_sess =
          CryptoVerification.E2E.Record.encodeRecord ⟨some sx⟩ :=
        encodeRecordX_eq_encodeRecord_pqSession x g_sess
      rw [← heq]; omega
    have hlen32_out : rec_out.length < 2 ^ 32 := by
      rw [hrec_out_eq]
      exact encodeRecord_storedSession_decryptW_lt_pure
        (cryptoOf' interp) (interpW interp) interp pureSerializeRole msg role.peer role
        coins_eff sx hdrcaps_sx hooo_in henc_sx_lt
    have hpq'_lt : slots_NonEmptyV1Q s'.pqRatchetState := by
      have hle := pq_length_le_encodeRecord_pure
        { sx with state := s', pendingPreKey := none, pendingKyberPreKey := none }
      have hlt : (CryptoVerification.E2E.Record.encodeRecord
          ⟨some { sx with state := s', pendingPreKey := none, pendingKyberPreKey := none }⟩).length <
          2 ^ 32 := by
        rwa [← hstored_eq, ← hrec_out_eq]
      change s'.pqRatchetState.length < 2 ^ 32
      dsimp at hle
      omega
    obtain ⟨hscopeP', hdeserP'⟩ :=
      deserializeScopeP_Q_storedSession_of_decryptW hrcq_sx.2.1 hdec_eff hpq'_lt
    let sess_out := storedSession sx
      (messageDecryptSignalW (cryptoOf' interp) (interpW interp)
        (pureSpqr (spqrModelOf interp)) pureSerializeRole (inMemAnswers sx) msg
        role.peer role coins_eff).2
    have hscopeP'_stored : slots_RecordInScopeP ⟨some sess_out⟩ := by
      dsimp [sess_out]; rwa [hstored_eq]
    have hdeserP'_stored : slots_DeserializeScopeP_Q slots_NonEmptyV1Q ⟨some sess_out⟩ := by
      dsimp [sess_out]; rwa [hstored_eq]
    have hq'_stored : slots_NonEmptyV1Q sess_out.state.pqRatchetState := by
      dsimp [sess_out]; rw [hstored_eq]; exact hpq'_lt
    have hbin'_stored : PureBinCanonSession sess_out :=
      pureBinCanonSession_of_deserializeScopeP_Q_any hdeserP'_stored
    have hrecScope'_stored : slots_RecordScopeP slots_NonEmptyV1Q ⟨some sess_out⟩ := by
      intro s hs; injection hs with hs'; subst hs'; exact hq'_stored
    have hrem_stored : sess_out.state.remoteIdentity.isSome = true := by
      dsimp [sess_out]; rw [hstored_eq]; dsimp; rw [hrem_s']; rfl
    have hppk_stored : sess_out.pendingPreKey = none := by
      dsimp [sess_out]; rw [hstored_eq]
    have hwrc : WireRecCanon rec_out :=
      ⟨sess_out, ⟨hrec_out_eq, hdeserP'_stored, hbin'_stored⟩,
        hscopeP'_stored, hrecScope'_stored, hrem_stored, by omega, hppk_stored⟩
    have hooo_stored : SpqrOooBounded sess_out.state.pqRatchetState :=
      spqrOooBounded_storedSession_decryptW_pure (cryptoOf' interp) (interpW interp) interp
        pureSerializeRole msg role.peer role coins_eff sx hooo_in hpqlen_in
    have htrCanon : rec_out.length < 2 ^ 32 - 2 ^ 20 → TRRecordCanon r p rec_out :=
      trRecordCanon_of_pureWireRecCanon_pqInj r p hwrc hrec_out_eq hooo_stored
    have heval : pureEvalRecvWireWithCoinsW (cryptoOf' interp) (interpW interp)
        (spqrModelOf interp) g_rw coins_eff = some (rec_out, pt) := by
      have hopen : evalOpen who_bv sx = some (role, sx) := by
        simp [evalOpen, hrole_who]
      simp only [pureEvalRecvWireWithCoinsW, g_rw, wireWhisperTag, htry, hopen]
      rcases hmd : messageDecryptSignalW (cryptoOf' interp) (interpW interp)
          (pureSpqr (spqrModelOf interp)) pureSerializeRole (inMemAnswers sx) msg
          role.peer role coins_eff with ⟨res_md, calls_md⟩
      have hres_md : res_md = .ok pt := by rw [← hok1, hmd]
      subst hres_md
      have hcalls_eq : calls_md = (messageDecryptSignalW (cryptoOf' interp) (interpW interp)
          (pureSpqr (spqrModelOf interp)) pureSerializeRole (inMemAnswers sx) msg
          role.peer role coins_eff).2 := by rw [hmd]
      dsimp only
      rw [hcalls_eq, ← hrec_out_eq]
    exact ⟨hlen32_out, hwrc, htrCanon, heval⟩
  let c_call := cliRecvWhisperCall p st body rc
  let i_call := pqRecvInputs W st (wireWhisper :: body) rc
  let o_call := pqxdhExpectedOutcome W i_call (some (some (st', pt)))
  have hev_acc : cliOutcomeEvents c_call (some o_call) =
      cliEntryEvents c_call ++ cliExitEvents c_call 0 pt := by
    simp [o_call, pqxdhExpectedOutcome, observe, cliOutcomeEvents]
  have hcs_mid : CoinSplit (cliOutcomeEvents c_call (some o_call))
      (.recv (wireWhisperTag :: body) ::
        (pqRecvWhisperMid interp st body (HMAC.keyToBytes32 rc) ++ [.accept pt])) := by
    rw [hev_acc]
    exact coinSplit_recvWhisper_accept_mid interp st body pt rfl rfl (keyToBytes32_ne_nil rc)
  by_cases hdraws : pureDrawsCoins (cryptoOf' interp) sx.state msg.senderRatchetKey = true
  · have hdraws_g : pureDrawsCoins (cryptoOf' interp) g_sess.session
        msg.senderRatchetKey = true := hdraws
    have hmid_eq : pqRecvWhisperMid interp st body (HMAC.keyToBytes32 rc) =
        [.rng (HMAC.keyToBytes32 rc)] := by
      simp [pqRecvWhisperMid, hsess, htry, hdraws_g]
    have hpin : Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepPure.purePinCoins (some (HMAC.keyToBytes32 rc)) =
        rc := by
      change pureCoinsOf (HMAC.keyToBytes32 rc) = rc
      exact coinsOf_keyToBytes32 rc
    obtain ⟨hlen32_out, hwrc, htrCanon, heval⟩ := hpost_for_coins rc hdecW_rc
    refine ⟨x, g_sess, s', k, msg, g_rw, [.rng (HMAC.keyToBytes32 rc)], rc,
      rfl, hst'.symm, hrec_p, hrec_ne, hss, hcanonP, hrec4, hlen31, hlen32_out, hpt_lt, hwrc,
      htrCanon, hmid_eq.symm, Or.inr rfl, hmid_eq ▸ hcs_mid, hwho_grw, rfl, hrcq_sx,
      Or.inr ⟨HMAC.keyToBytes32 rc, rfl, keyToBytes32_length rc, hpin.symm, fun m0 hm0 => ?_⟩,
      fun m0 hm0 => ?_, heval⟩
    · cases hm0; exact hdraws
    · cases hm0
      change Symbolic.Swarm.CREF.CliPure.TR.PureRecvEval.PureDecryptCoinsOk (cryptoOf' interp)
        sx.state msg.senderRatchetKey rc
      rw [← coinsOf_keyToBytes32 rc]
      exact Symbolic.Swarm.CREF.CliPure.TR.PureRecvEval.pureDecryptCoinsOk_of_draws_true
        hdraws (keyToBytes32_length rc)
  · have hdraws_f : pureDrawsCoins (cryptoOf' interp) sx.state msg.senderRatchetKey = false :=
      Bool.eq_false_iff.mpr hdraws
    have hdraws_g : pureDrawsCoins (cryptoOf' interp) g_sess.session
        msg.senderRatchetKey = false := hdraws_f
    have hmid_eq : pqRecvWhisperMid interp st body (HMAC.keyToBytes32 rc) = [] := by
      simp [pqRecvWhisperMid, hsess, htry, hdraws_g]
    have hdecW_zero : Proofs.libsignal.SR.SessionState.tryDecryptFromRecordW (cryptoOf' interp)
        (interpW interp) (pureSpqr (spqrModelOf interp))
        (pureSerializeRole role.peer role) msg .whisper 0#256 sx.state =
        (.ok pt, s') := by
      rwa [← tryDecryptFromRecordW_coins_irrel_of_pureDrawsCoins_false (cryptoOf' interp)
        (interpW interp) (pureSpqr (spqrModelOf interp)) _ msg .whisper rc 0#256 sx.state
        hrem_sx hdraws_f]
    obtain ⟨hlen32_out, hwrc, htrCanon, heval⟩ := hpost_for_coins 0#256 hdecW_zero
    have hmiss : recvWireMissFactPure (cryptoOf' interp) (interpW interp) (spqrModelOf interp)
        g_rw := by
      intro _res _hr b0 m0 hw0 hp0 _hv0
      change wireWhisperTag :: body = wireWhisperTag :: b0 at hw0
      injection hw0 with _ hb0; subst hb0
      rw [htry] at hp0; cases hp0
      exact hdraws_f
    refine ⟨x, g_sess, s', k, msg, g_rw, [], 0#256,
      rfl, hst'.symm, hrec_p, hrec_ne, hss, hcanonP, hrec4, hlen31, hlen32_out, hpt_lt, hwrc,
      htrCanon, hmid_eq.symm, Or.inl rfl, hmid_eq ▸ hcs_mid, hwho_grw, rfl, hrcq_sx,
      Or.inl ⟨rfl, rfl, hmiss⟩,
      fun m0 hm0 => ?_, heval⟩
    cases hm0
    change Symbolic.Swarm.CREF.CliPure.TR.PureRecvEval.PureDecryptCoinsOk (cryptoOf' interp)
      sx.state msg.senderRatchetKey 0#256
    exact Symbolic.Swarm.CREF.CliPure.TR.PureRecvEval.pureDecryptCoinsOk_of_draws_false hdraws_f

end Symbolic.Swarm.CREF.Cli.Slots
