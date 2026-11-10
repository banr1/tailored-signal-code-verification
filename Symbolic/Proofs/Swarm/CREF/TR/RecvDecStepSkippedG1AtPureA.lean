/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.PkDispatchAtPure
public import Symbolic.Proofs.Swarm.TRREF.SpqrSemOf
public import Symbolic.Proofs.Swarm.CREF.TR.SrHonestVer
import Batteries.Data.UInt
import DY.Bytes.Basic
import DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Bytes.Basic
public import Symbolic.Proofs.Swarm.CREF.TR.PureCanon
public import Symbolic.Proofs.Swarm.CREF.TR.SpqrSemDef
public import Symbolic.Proofs.Swarm.TRREF.B3DefsPure
import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.SymEnc
import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.TrWireMsg
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepSpqrHonestPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.SendRetCoinsCliPureB
import Symbolic.Proofs.Swarm.CREF.Initiate.InitRej
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.PQGamma
import Symbolic.Proofs.Swarm.CREF.TR.PureRecvStepBridge
import Symbolic.Proofs.Swarm.CREF.TR.RecvRep
import Symbolic.Proofs.Swarm.CREF.TROpen
import Symbolic.Proofs.Swarm.CREF.TR.Leaks -- shake: keep
import Symbolic.Proofs.Swarm.CREF.TR.PQModelRunNil -- shake: keep
public import Symbolic.Proofs.Swarm.CREF.TR.RecvCol -- shake: keep

/-!
# Cached Skipped-Key Decrypt Witnesses

Proves decrypt-witness lemmas at a fixed `(g, t)` explanation for the cached skipped-key
whisper receive branch.
-/

@[expose] public section

cref_hide_foreign_instances

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.dupNamespace false

namespace Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepAtPure
open Symbolic.Swarm.CREF.TR hiding at?_append_of_lt compromisesCurrentFrom_append forall₂_append gamma_concat getLocalState_fst getLocalState_snd leValue_leBytes length_leBytes newRandoms_append_rnd ownSaltsFrom_append p25519_lt p25519_pos runMoves_append runTrace_append runTrace_snoc runVis_append runVis_snoc run_bind_fst run_bind_snd uOf_leBytes uOf_lt
open Symbolic.Swarm.CREF.TR.RecvDecStep
open Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep hiding SpqrSem StEntry TREntry
open Symbolic.Swarm.CREF.CliPure.TR.RecvDecStepAt

cref_open
cref_open_tr

open DY DY.Comparse DY.Literal DY.Libsignal DY.DiffieHellman
open DY.Libsignal.TripleRatchet (computeMac messageVersion)
open DY.Libsignal.Refinement (aesCbcDecryptSymbol ExternCryptoLawsHold)
open DY.Libsignal.TripleRatchet
open DY.Libsignal.HwEvents DY.Libsignal.Rust
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E CryptoVerification.E2E.InMem CryptoVerification.E2E.Record CryptoVerification.E2E.RecordX
open CryptoVerification.E2E.Pqxdh.WireEntries.SymP3 (RecvWireGhost)
open CryptoProofLib.Refinement (ExternInterpretation)
open Proofs.libsignal.RngG Proofs.libsignal.RngG.CliPure.R3
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure Symbolic.Swarm.CREF.CliPureRcv
open Symbolic.Swarm.CREF.CliPure.TR Symbolic.Swarm.CREF.CliPureRcv.TR
open Symbolic.Swarm.CREF.TR.FreshSigma
open Symbolic.Swarm.TRREF.SpqrSemOf (spqrModelOf saltToBytes)
open Symbolic.Swarm.CREF.TR.RecvRep hiding gamma_litOf
open Symbolic.Swarm.CREF.TR.RecvDec hiding StEntry TREntry TRRecvAllCollide
open Symbolic.Swarm.CREF.CliPure.TR.SendRetCoins (gamma_symEnc_tr gamma_kdfExtract_tr
  gamma_trunc8_tr)

theorem gamma_trMsgKeys_congr (interpretation : ExternInterpretation) (S : SpqrSem) (g : Ghost)
    (s₁ s₂ seed : DY.Bytes) (hs : gamma interpretation S g s₁ = gamma interpretation S g s₂) :
    gamma interpretation S g (trMsgKeys s₁ seed).cipherKey = gamma interpretation S g (trMsgKeys s₂ seed).cipherKey ∧
    gamma interpretation S g (trMsgKeys s₁ seed).macKey = gamma interpretation S g (trMsgKeys s₂ seed).macKey ∧
    gamma interpretation S g (trMsgKeys s₁ seed).iv = gamma interpretation S g (trMsgKeys s₂ seed).iv :=
  Symbolic.Swarm.CREF.TR.G1.gamma_trMsgKeys_eq_of_gamma_eq interpretation S g hs rfl

theorem gamma_computeMac_congr_key (interpretation : ExternInterpretation) (S : SpqrSem) (g : Ghost)
    (mk₁ mk₂ peerIk myIk wire : DY.Bytes) (hmk : gamma interpretation S g mk₁ = gamma interpretation S g mk₂) :
    gamma interpretation S g (computeMac mk₁ peerIk myIk wire) = gamma interpretation S g (computeMac mk₂ peerIk myIk wire) := by
  unfold DY.Libsignal.TripleRatchet.computeMac DY.Libsignal.TripleRatchet.hmac
  rw [SendRetCoins.gamma_trunc8_tr, SendRetCoins.gamma_trunc8_tr,
      SendRetCoins.gamma_kdfExtract_tr, SendRetCoins.gamma_kdfExtract_tr, hmk]

abbrev AuthenticDecryptRepB3_g1 := AuthenticDecryptRepB3AtSt

theorem honestSend_pqRatchet_witness_of_pqFromHonest_tr (interpretation : ExternInterpretation) (r₀ : ProtocolSetup) (S : SpqrSem)
    (g : Ghost) (ms₁ : List Move) (evs : List MachineEvent) (sent : List HwBytes) (body : HwBytes) (m : SignalMessage)
    {who : List Participant}
    (hmp : MatchedPrefix interpretation r₀ S who g ms₁ evs) (hfit : SrHonestVer.SendsFit evs)
    (hsent : sent = sentBodies evs) (hpq : PqFromHonest sent body)
    (htry : SignalMessage.tryFrom protoSignalCodec body = .ok m) :
    ∃ (st_s : TRState) (t_c coinsLen : Nat), st_s ∈ availableStates r₀ (runTraceMoves r₀ ms₁) ∧
      (DY.Spqr.spqrSend st_s.spqr (randTerm t_c coinsLen)).2.2.AttackerKnows (runTraceMoves r₀ ms₁) ∧
      gamma interpretation S g (DY.Spqr.spqrSend st_s.spqr (randTerm t_c coinsLen)).2.2 = m.pqRatchet ∧
      DY.Spqr.spqrEmptyMsg (DY.Spqr.spqrSend st_s.spqr (randTerm t_c coinsLen)).2.2 = false := by
  have hHon : PqFromHonest (sentBodies evs) body := hsent ▸ hpq
  obtain ⟨st_s, coins_s, st, ts, coinsLen, hpq_kn, hpq_gam, hst_avail, rfl, rfl⟩ :=
    SrHonestVer.exists_honest_sendMsg_of_pqFromHonest_prov interpretation r₀ S g ms₁ evs body m hmp hfit hHon htry
  refine ⟨st, ts + 1, coinsLen, hst_avail, hpq_kn, hpq_gam, ?_⟩
  dsimp only [DY.Spqr.spqrEmptyMsg, DY.Literal.bytesToLiteral, DY.Literal.CanMkLiteral.bytesToLiteral,
    DY.Spqr.spqrSend, DY.Spqr.SendMsg.SubF.pack]
  rw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Literal.Literal.SubF]

theorem length_gamma_hmac_tr_g1 (interpretation : ExternInterpretation) (S : SpqrSem) (g : Ghost)
    (k m : DY.Bytes) :
    (gamma interpretation S g (DY.Libsignal.TripleRatchet.hmac k m)).length = 32 := by
  change (gamma interpretation S g (DY.KdfExtract.kdfExtract k m)).length = 32
  rw [gamma_kdfExtract_tr]
  exact Symbolic.Swarm.CREF.TR.length_hmacWith _ _ _

theorem forged_decrypt_rep_of_seedKnown_with_sendMsg_tr_at
    (interpretation : ExternInterpretation) (hCrypto : ExternCryptoLawsHold interpretation)
    (r₀ : ProtocolSetup) (S : SpqrSem) (g : Ghost) (ms₁ : List Move) (body pt : HwBytes) (st_in : TRState)
    (t₀ : DY.Bytes) (msg₀ : TRSignalMsg) (m : SignalMessage)
    (rk seed pq_t : DY.Bytes) (pqrKey : HKDF.Salt) (htry : SignalMessage.tryFrom protoSignalCodec body = .ok m)
    (ht₀ : t₀ ∈ recvRepresentations interpretation r₀ S g ms₁ body) (hparse₀ : parseTrSignalMsg t₀ = some msg₀)
    (hver₀ : msg₀.version = messageVersion) (hrk₀ : msg₀.ratchetKey = rk)
    (hpq_kn : pq_t.AttackerKnows (runTraceMoves r₀ ms₁)) (hpq_gam : gamma interpretation S g pq_t = m.pqRatchet)
    (hseed_kn : seed.AttackerKnows (runTraceMoves r₀ ms₁))
    (hPeerK : st_in.peerIk.AttackerKnows (runTraceMoves r₀ ms₁)) (hMyK : st_in.myIk.AttackerKnows (runTraceMoves r₀ ms₁))
    (hMacBytes : body.drop (body.length - 8) =
      gamma interpretation S g (computeMac (trMsgKeys (litOf (spqrKeyBytes (saltToBytes pqrKey))) seed).macKey st_in.peerIk st_in.myIk msg₀.wire))
    (hDecOk : interpretation aesCbcDecryptSymbol
      [m.ciphertext, gamma interpretation S g (trMsgKeys (litOf (spqrKeyBytes (saltToBytes pqrKey))) seed).cipherKey,
       (gamma interpretation S g (trMsgKeys (litOf (spqrKeyBytes (saltToBytes pqrKey))) seed).iv).take 16] = some pt) :
    ∃ (t' : DY.Bytes) (msg' : TRSignalMsg) (pqSalt ptTerm : DY.Bytes),
      t' ∈ recvRepresentations interpretation r₀ S g ms₁ body ∧ pqSalt.AttackerKnows (runTraceMoves r₀ ms₁) ∧ t'.AttackerKnows (runTraceMoves r₀ ms₁) ∧
      parseTrSignalMsg t' = some msg' ∧ msg'.version = messageVersion ∧ msg'.ratchetKey = rk ∧ msg'.counter = msg₀.counter ∧ msg'.pqRatchet = pq_t ∧
      msg'.mac = computeMac (trMsgKeys pqSalt seed).macKey st_in.peerIk st_in.myIk msg'.wire ∧
      DY.SymEnc.symDec (trMsgKeys pqSalt seed).cipherKey (trMsgKeys pqSalt seed).iv msg'.ciphertext = some ptTerm ∧
      gamma interpretation S g t' = body ∧ gamma interpretation S g ptTerm = pt ∧
      gamma interpretation S g pqSalt = spqrKeyBytes (saltToBytes pqrKey) := by
  let tr := runTraceMoves r₀ ms₁
  let pqSalt := litOf (spqrKeyBytes (saltToBytes pqrKey))
  let ptTerm := litOf pt
  let ct' := DY.SymEnc.symEnc (trMsgKeys pqSalt seed).cipherKey (trMsgKeys pqSalt seed).iv ptTerm
  have hpqSalt_kn : pqSalt.AttackerKnows tr := knows_litOf _ _
  have hpqSalt_gam : gamma interpretation S g pqSalt = spqrKeyBytes (saltToBytes pqrKey) := gamma_litOf interpretation S g _
  have hprk_kn : (DY.Libsignal.TripleRatchet.hmac pqSalt seed).AttackerKnows tr :=
    KdfExtract.attacker_knows_kdfExtract _ _ _ hpqSalt_kn hseed_kn
  have hinfo_kn : (DY.Libsignal.TripleRatchet.lit "WhisperMessageKeys").AttackerKnows tr :=
    Literal.attacker_knows_literalToBytes _ _
  have hck_kn : (trMsgKeys pqSalt seed).cipherKey.AttackerKnows tr :=
    KdfExtract.attacker_knows_kdfExtract _ _ _ hprk_kn
      (Concat.attacker_knows_concat _ _ _ hinfo_kn (Literal.attacker_knows_literalToBytes _ _))
  have hmk_kn : (trMsgKeys pqSalt seed).macKey.AttackerKnows tr :=
    KdfExtract.attacker_knows_kdfExtract _ _ _ hprk_kn
      (Concat.attacker_knows_concat _ _ _ hck_kn
        (Concat.attacker_knows_concat _ _ _ hinfo_kn (Literal.attacker_knows_literalToBytes _ _)))
  have hiv_kn : (trMsgKeys pqSalt seed).iv.AttackerKnows tr :=
    KdfExtract.attacker_knows_kdfExtract _ _ _ hprk_kn
      (Concat.attacker_knows_concat _ _ _ hmk_kn
        (Concat.attacker_knows_concat _ _ _ hinfo_kn (Literal.attacker_knows_literalToBytes _ _)))
  have hct'_kn : ct'.AttackerKnows tr :=
    DY.SymEnc.attacker_knows_symEnc _ _ _ tr hck_kn hiv_kn (knows_litOf pt _)
  have hwire₀_kn : msg₀.wire.AttackerKnows tr := by
    have hsp := Concat.attacker_knows_split t₀ (t₀.length - Trunc.trunc8Length) tr ht₀.1
    unfold parseTrSignalMsg at hparse₀
    rcases hsplit : Concat.split t₀ (t₀.length - Trunc.trunc8Length) with _ | ⟨w₀, m₀⟩
    · rw [hsplit] at hparse₀; cases hparse₀
    · rw [hsplit] at hsp hparse₀; dsimp only [Bind.bind, Option.bind] at hparse₀
      rcases hwf : DY.TrWire.trWireMsgFields? w₀ with _ | x₀
      · rw [hwf] at hparse₀; cases hparse₀
      · rw [hwf] at hparse₀; injection hparse₀ with hmsg; subst hmsg; exact hsp.1
  obtain ⟨v₀, pc₀, ev₀, hwire₀_eq, _⟩ :=
    Symbolic.Swarm.CREF.TR.G1.parseTrSignalMsg_eq_some_inv hparse₀
  have hargs₀ := DY.TrWire.attacker_knows_trWireMsg_args v₀ msg₀.ratchetKey msg₀.counter pc₀
    msg₀.ciphertext msg₀.pqRatchet ev₀ tr (hwire₀_eq ▸ hwire₀_kn)
  obtain ⟨hwire₀_take, _, _, htry₀⟩ := ht₀.2.2.2 msg₀ hparse₀
  obtain ⟨_, hrk₀_gam, _, hctr₀_nat, hver₀_nat⟩ := htry₀ m htry
  have hck_len : (gamma interpretation S g (trMsgKeys pqSalt seed).cipherKey).length = 32 :=
    length_gamma_hmac_tr_g1 interpretation S g _ _
  have hiv_len32 : (gamma interpretation S g (trMsgKeys pqSalt seed).iv).length = 32 :=
    length_gamma_hmac_tr_g1 interpretation S g _ _
  have hiv_len : ((gamma interpretation S g (trMsgKeys pqSalt seed).iv).take 16).length = 16 := by
    rw [List.length_take, hiv_len32]; omega
  have hct'_gam : gamma interpretation S g ct' = m.ciphertext := by
    dsimp only [ct', ptTerm]
    rw [gamma_symEnc_tr, gamma_litOf,
        hCrypto.aes_cbc_encrypt_of_decrypt _ _ _ _ hck_len hiv_len hDecOk, Option.getD_some]
  obtain ⟨v, _, hwire'_kn, hwire'_take, _, _, hforged⟩ :=
    exists_trWire_rep_with_pqTerm interpretation r₀ S g ms₁ body m htry
      msg₀.ratchetKey ct' pq_t hargs₀.1 hct'_kn hpq_kn hrk₀_gam hct'_gam
  let wire' := DY.TrWire.trWireMsg (UInt8.ofNat m.messageVersion.toNat) msg₀.ratchetKey
    (UInt32.ofNat m.counter.toNat)
    (UInt32.ofNat m.previousCounter.toNat)
    ct' pq_t v
  let mac' := computeMac (trMsgKeys pqSalt seed).macKey st_in.peerIk st_in.myIk wire'
  have hmac'_kn : mac'.AttackerKnows tr :=
    attackerKnows_computeMac_tr tr _ _ _ _ hmk_kn hPeerK hMyK hwire'_kn
  have hmac'_len : mac'.length = Trunc.trunc8Length := length_computeMac_tr _ _ _ _
  have hmac'_gam : gamma interpretation S g mac' = body.drop (body.length - 8) := by
    rw [hMacBytes]; dsimp only [mac']
    exact gamma_computeMac_congr_wire interpretation S g _ _ _ wire' msg₀.wire (hwire'_take.trans hwire₀_take.symm)
  obtain ⟨ht'_kn, ht'_gam, hparse', hver', hrk', hctr', hct', hpq', hmem_fn⟩ :=
    hforged mac' hmac'_kn hmac'_len hmac'_gam (by
      dsimp only [mac', DY.Libsignal.TripleRatchet.computeMac, DY.Trunc.trunc8, DY.Trunc.CanTrunc8.trunc8,
        DY.Trunc.Trunc8.SubF.pack, spqrHeaded]
      rw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Spqr.InitState.SubF,
          Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Spqr.SendState.SubF,
          Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Spqr.SendKey.SubF,
          Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Spqr.SendMsg.SubF,
          Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Spqr.RecvState.SubF,
          Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Spqr.RecvKey.SubF,
          Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Spqr.ChainKey.SubF]
      rfl)
  refine ⟨Concat.concat wire' mac', _, pqSalt, ptTerm, hmem_fn hpq_gam, hpqSalt_kn, ht'_kn,
    hparse', (UInt8.ext (hver'.trans hver₀_nat.symm)).trans hver₀, hrk'.trans hrk₀,
    UInt32.ext (hctr'.trans hctr₀_nat.symm), hpq', rfl, ?_, ht'_gam,
    gamma_litOf interpretation S g pt, hpqSalt_gam⟩
  rw [hct']; exact DY.SymEnc.symDec_symEnc _ _ _

theorem authentic_decrypt_witness_of_not_empty_nw
    (interpretation : ExternInterpretation) (hCrypto : ExternCryptoLawsHold interpretation)
    (r₀ : ProtocolSetup) (S : SpqrSem) (hS : S = compSemOf interpretation r₀) (g : Ghost) (p : Participant)
    (stateIdx : Nat) (ms₁ : List Move)
    (recBytes body pt : HwBytes) (rec : RecordRec) (st st_in st_prov : TRState) (g_rw : RecvWireGhost)
    (t₀ : DY.Bytes) (msg₀ : TRSignalMsg) (m : SignalMessage)
    (rk seed salt : DY.Bytes) (newPqrState : HwBytes) (pqrKey : HKDF.Salt) (st_s : TRState) (t_c coinsLen : Nat)
    (hrecBytes : recBytes = recordBytes rec) (hrel : StateRel interpretation S g st rec)
    (hspqr_eq : st_in.spqr = st.spqr) (hpeer_eq : st_prov.peerIk = st_in.peerIk) (hmy_eq : st_prov.myIk = st_in.myIk)
    (hst : ((PersistentLocalState.getLocalState p stateIdx : Traceful TRState).run (runTraceMoves r₀ ms₁)).1 = some st)
    (hcanon_q : TR.Pure.slots_RecordCanonical_Q TR.Pure.slots_NonEmptyV1Q recBytes g_rw.sess) (htry : SignalMessage.tryFrom protoSignalCodec body = .ok m)
    (ht₀ : t₀ ∈ recvRepresentations interpretation r₀ S g ms₁ body) (hparse₀ : parseTrSignalMsg t₀ = some msg₀)
    (hver₀ : msg₀.version = messageVersion) (hrk₀ : msg₀.ratchetKey = rk)
    (hPeerK : st_prov.peerIk.AttackerKnows (runTraceMoves r₀ ms₁)) (hMyK : st_prov.myIk.AttackerKnows (runTraceMoves r₀ ms₁))
    (hrecv_spqr : (Symbolic.Swarm.TRREF.SpqrSemOf.spqrModelOf interpretation).recv g_rw.sess.state.pqRatchetState m.pqRatchet = .ok (newPqrState, pqrKey))
    (hAuth : AuthenticDecryptRepB3_g1 interpretation r₀ S g ms₁ body pt t₀ msg₀ st_prov salt seed)
    (hMacBytes_salt : body.drop (body.length - 8) = gamma interpretation S g (computeMac (trMsgKeys salt seed).macKey st_prov.peerIk st_prov.myIk msg₀.wire))
    (hDecOk_salt : interpretation aesCbcDecryptSymbol
      [m.ciphertext, gamma interpretation S g (trMsgKeys salt seed).cipherKey,
       (gamma interpretation S g (trMsgKeys salt seed).iv).take 16] = some pt)
    (hempty : DY.Spqr.spqrEmptyMsg msg₀.pqRatchet = false) (hst_s : st_s ∈ availableStates r₀ (runTraceMoves r₀ ms₁))
    (hpq_eq : msg₀.pqRatchet = (DY.Spqr.spqrSend st_s.spqr (randTerm t_c coinsLen)).2.2) :
    ∃ (t' : DY.Bytes) (msg' : TRSignalMsg) (pqSalt ptTerm spqr' key : DY.Bytes) (spqrMsgIdx : UInt32),
      t' ∈ recvRepresentations interpretation r₀ S g ms₁ body ∧ pqSalt.AttackerKnows (runTraceMoves r₀ ms₁) ∧ t'.AttackerKnows (runTraceMoves r₀ ms₁) ∧
      parseTrSignalMsg t' = some msg' ∧ msg'.version = messageVersion ∧ msg'.ratchetKey = rk ∧ msg'.counter = msg₀.counter ∧
      Spqr.spqrRecv st_in.spqr msg'.pqRatchet spqrMsgIdx = some (spqr', key) ∧ gamma interpretation S g spqr' = newPqrState ∧
      msg'.mac = computeMac (trMsgKeys pqSalt seed).macKey st_in.peerIk st_in.myIk msg'.wire ∧
      DY.SymEnc.symDec (trMsgKeys pqSalt seed).cipherKey (trMsgKeys pqSalt seed).iv msg'.ciphertext = some ptTerm ∧
      gamma interpretation S g t' = body ∧ gamma interpretation S g ptTerm = pt ∧
      msg'.pqRatchet = (DY.Spqr.spqrSend st_s.spqr (randTerm t_c coinsLen)).2.2 := by
  obtain ⟨_, _, _, _, _, _, pqSalt, ptTerm, hpqSalt_kn, hmac₀, hdec₀, hpt_gam⟩ := hAuth
  obtain ⟨_, hOut⟩ := PureRecvEval.spqrRecv_step_bridge_of_not_empty_pending_pure interpretation hCrypto r₀ S hS g ms₁ p stateIdx
    recBytes body rec st st_in g_rw t₀ msg₀ m newPqrState pqrKey
    hst hrecBytes hrel hspqr_eq hcanon_q ht₀ hparse₀ htry hempty hrecv_spqr
  obtain ⟨spqrMsgIdx, spqr', key, hspqr_step, hspqr'_gam, _⟩ := hOut.exists_step
  rw [hpeer_eq, hmy_eq] at hmac₀
  exact ⟨t₀, msg₀, pqSalt, ptTerm, spqr', key, spqrMsgIdx,
    ht₀, hpqSalt_kn, ht₀.1, hparse₀, hver₀, hrk₀, rfl,
    hspqr_step, hspqr'_gam, hmac₀, hdec₀, ht₀.2.1, hpt_gam, hpq_eq⟩

/-- Fixed-`(g, t)` decrypt witness in the `seed.AttackerKnows` branch. -/
theorem skipped_decryptWitness_of_seedKnown_at
    (interpretation : ExternInterpretation) (hCrypto : ExternCryptoLawsHold interpretation)
    (r₀ : ProtocolSetup) (S : SpqrSem) (hS : S = compSemOf interpretation r₀)
    (g : Ghost) (p : Participant) (stateIdx : Nat) (ms₁ : List Move) (evs : List MachineEvent) (sent : List HwBytes)
    (recBytes body pt : HwBytes) (rec : RecordRec) (st st_in st_prov : TRState) (g_rw : RecvWireGhost)
    (t₀ : DY.Bytes) (msg₀ : TRSignalMsg) (m : SignalMessage) (rk seed k_own : DY.Bytes) (newPqrState : HwBytes) (pqrKey : HKDF.Salt)
    {who : List Participant}
    (hmp : MatchedPrefix interpretation r₀ S who g ms₁ evs) (hfit : SrHonestVer.SendsFit evs) (hsent : sent = sentBodies evs)
    (hrecBytes : recBytes = recordBytes rec) (hrel : StateRel interpretation S g st rec) (hspqr_eq : st_in.spqr = st.spqr)
    (hst : ((PersistentLocalState.getLocalState p stateIdx : Traceful TRState).run (runTraceMoves r₀ ms₁)).1 = some st)
    (hcanon_q : TR.Pure.slots_RecordCanonical_Q TR.Pure.slots_NonEmptyV1Q recBytes g_rw.sess) (hpq : PqFromHonest sent body)
    (htry : SignalMessage.tryFrom protoSignalCodec body = .ok m) (ht₀ : t₀ ∈ recvRepresentations interpretation r₀ S g ms₁ body)
    (hparse₀ : parseTrSignalMsg t₀ = some msg₀) (hver₀ : msg₀.version = messageVersion) (hrk₀ : msg₀.ratchetKey = rk)
    (hIkEq : st_prov.peerIk = st_in.peerIk ∧ st_prov.myIk = st_in.myIk)
    (hk_own_gam : gamma interpretation S g k_own = spqrKeyBytes (saltToBytes pqrKey))
    (hMacBytes : body.drop (body.length - 8) = gamma interpretation S g (computeMac (trMsgKeys k_own seed).macKey st_prov.peerIk st_prov.myIk msg₀.wire))
    (hPeerK : st_prov.peerIk.AttackerKnows (runTraceMoves r₀ ms₁)) (hMyK : st_prov.myIk.AttackerKnows (runTraceMoves r₀ ms₁))
    (hDecOk : interpretation aesCbcDecryptSymbol
      [m.ciphertext, gamma interpretation S g (trMsgKeys k_own seed).cipherKey,
       (gamma interpretation S g (trMsgKeys k_own seed).iv).take 16] = some pt)
    (hrecv_spqr : (Symbolic.Swarm.TRREF.SpqrSemOf.spqrModelOf interpretation).recv g_rw.sess.state.pqRatchetState m.pqRatchet = .ok (newPqrState, pqrKey))
    (hseed_kn : seed.AttackerKnows (runTraceMoves r₀ ms₁)) :
    ∃ (t' : DY.Bytes) (msg' : TRSignalMsg) (pqSalt ptTerm spqr' key : DY.Bytes) (spqrMsgIdx : UInt32),
      t' ∈ recvRepresentations interpretation r₀ S g ms₁ body ∧ pqSalt.AttackerKnows (runTraceMoves r₀ ms₁) ∧ t'.AttackerKnows (runTraceMoves r₀ ms₁) ∧
      parseTrSignalMsg t' = some msg' ∧ msg'.version = messageVersion ∧ msg'.ratchetKey = rk ∧ msg'.counter = msg₀.counter ∧
      Spqr.spqrRecv st_in.spqr msg'.pqRatchet spqrMsgIdx = some (spqr', key) ∧ gamma interpretation S g spqr' = newPqrState ∧
      msg'.mac = computeMac (trMsgKeys pqSalt seed).macKey st_in.peerIk st_in.myIk msg'.wire ∧
      DY.SymEnc.symDec (trMsgKeys pqSalt seed).cipherKey (trMsgKeys pqSalt seed).iv msg'.ciphertext = some ptTerm ∧
      gamma interpretation S g t' = body ∧ gamma interpretation S g ptTerm = pt := by
  obtain ⟨st_s, t_c, coinsLen, _hst_s, hpq_kn, hpq_gam, hempty_pq⟩ :=
    honestSend_pqRatchet_witness_of_pqFromHonest_tr interpretation r₀ S g ms₁ evs sent body m hmp hfit hsent hpq htry
  let pq_t := (DY.Spqr.spqrSend st_s.spqr (randTerm t_c coinsLen)).2.2
  let pqSalt_lit := litOf (spqrKeyBytes (saltToBytes pqrKey))
  have hpqSalt_lit_gam : gamma interpretation S g pqSalt_lit = gamma interpretation S g k_own := by rw [gamma_litOf, hk_own_gam]
  have hmk_eq := gamma_trMsgKeys_congr interpretation S g pqSalt_lit k_own seed hpqSalt_lit_gam
  have hMacBytes_lit : body.drop (body.length - 8) =
      gamma interpretation S g (computeMac (trMsgKeys pqSalt_lit seed).macKey st_prov.peerIk st_prov.myIk msg₀.wire) := by
    rw [hMacBytes, gamma_computeMac_congr_key interpretation S g
      (trMsgKeys pqSalt_lit seed).macKey (trMsgKeys k_own seed).macKey st_prov.peerIk st_prov.myIk msg₀.wire hmk_eq.2.1]
  have hDecOk_lit : interpretation aesCbcDecryptSymbol
      [m.ciphertext, gamma interpretation S g (trMsgKeys pqSalt_lit seed).cipherKey,
       (gamma interpretation S g (trMsgKeys pqSalt_lit seed).iv).take 16] = some pt := by
    rw [hmk_eq.1, hmk_eq.2.2]; exact hDecOk
  obtain ⟨t', msg', pqSalt, ptTerm, ht'_rep, hpqSalt_kn, ht'_kn, hparse', hver', hrk', hctr',
      hpq_eq', hmac', hdec', ht'_gam, hpt_gam, _⟩ :=
    forged_decrypt_rep_of_seedKnown_with_sendMsg_tr_at interpretation hCrypto r₀ S g ms₁
      body pt st_prov t₀ msg₀ m rk seed pq_t pqrKey
      htry ht₀ hparse₀ hver₀ hrk₀ hpq_kn hpq_gam hseed_kn hPeerK hMyK hMacBytes_lit hDecOk_lit
  have hempty' : DY.Spqr.spqrEmptyMsg msg'.pqRatchet = false := by rw [hpq_eq']; exact hempty_pq
  obtain ⟨_, hOut⟩ := PureRecvEval.spqrRecv_step_bridge_of_not_empty_pending_pure interpretation hCrypto r₀ S hS g ms₁ p stateIdx
    recBytes body rec st st_in g_rw t' msg' m newPqrState pqrKey
    hst hrecBytes hrel hspqr_eq hcanon_q ht'_rep hparse' htry hempty' hrecv_spqr
  obtain ⟨spqrMsgIdx, spqr', key, hspqr_step, hspqr'_gam, _⟩ := hOut.exists_step
  rw [hIkEq.1, hIkEq.2] at hmac'
  exact ⟨t', msg', pqSalt, ptTerm, spqr', key, spqrMsgIdx,
    ht'_rep, hpqSalt_kn, ht'_kn, hparse', hver', hrk', hctr',
    hspqr_step, hspqr'_gam, hmac', hdec', ht'_gam, hpt_gam⟩

/-- Fixed-`(g, t)` decrypt witness in the `AuthenticDecryptRepB3_g1` branch. -/
theorem skipped_decryptWitness_of_authentic_at
    (interpretation : ExternInterpretation) (hCrypto : ExternCryptoLawsHold interpretation)
    (r₀ : ProtocolSetup) (S : SpqrSem) (hS : S = compSemOf interpretation r₀)
    (g : Ghost) (p : Participant) (stateIdx : Nat) (ms₁ : List Move)
    (recBytes body pt : HwBytes) (rec : RecordRec) (st st_in st_prov : TRState) (g_rw : RecvWireGhost)
    (t₀ : DY.Bytes) (msg₀ : TRSignalMsg) (m : SignalMessage) (rk seed salt : DY.Bytes) (newPqrState : HwBytes) (pqrKey : HKDF.Salt)
    (hrecBytes : recBytes = recordBytes rec) (hrel : StateRel interpretation S g st rec) (hspqr_eq : st_in.spqr = st.spqr)
    (hst : ((PersistentLocalState.getLocalState p stateIdx : Traceful TRState).run (runTraceMoves r₀ ms₁)).1 = some st)
    (hcanon_q : TR.Pure.slots_RecordCanonical_Q TR.Pure.slots_NonEmptyV1Q recBytes g_rw.sess)
    (htry : SignalMessage.tryFrom protoSignalCodec body = .ok m) (ht₀ : t₀ ∈ recvRepresentations interpretation r₀ S g ms₁ body)
    (hparse₀ : parseTrSignalMsg t₀ = some msg₀) (hver₀ : msg₀.version = messageVersion) (hrk₀ : msg₀.ratchetKey = rk)
    (hIkEq : st_prov.peerIk = st_in.peerIk ∧ st_prov.myIk = st_in.myIk)
    (hPeerK : st_prov.peerIk.AttackerKnows (runTraceMoves r₀ ms₁)) (hMyK : st_prov.myIk.AttackerKnows (runTraceMoves r₀ ms₁))
    (hrecv_spqr : (Symbolic.Swarm.TRREF.SpqrSemOf.spqrModelOf interpretation).recv g_rw.sess.state.pqRatchetState m.pqRatchet = .ok (newPqrState, pqrKey))
    (hAuth : AuthenticDecryptRepB3_g1 interpretation r₀ S g ms₁ body pt t₀ msg₀ st_prov salt seed)
    (hMacBytes_salt : body.drop (body.length - 8) = gamma interpretation S g (computeMac (trMsgKeys salt seed).macKey st_prov.peerIk st_prov.myIk msg₀.wire))
    (hDecOk_salt : interpretation aesCbcDecryptSymbol
      [m.ciphertext, gamma interpretation S g (trMsgKeys salt seed).cipherKey,
       (gamma interpretation S g (trMsgKeys salt seed).iv).take 16] = some pt) :
    ∃ (t' : DY.Bytes) (msg' : TRSignalMsg) (pqSalt ptTerm spqr' key : DY.Bytes) (spqrMsgIdx : UInt32),
      t' ∈ recvRepresentations interpretation r₀ S g ms₁ body ∧ pqSalt.AttackerKnows (runTraceMoves r₀ ms₁) ∧ t'.AttackerKnows (runTraceMoves r₀ ms₁) ∧
      parseTrSignalMsg t' = some msg' ∧ msg'.version = messageVersion ∧ msg'.ratchetKey = rk ∧ msg'.counter = msg₀.counter ∧
      Spqr.spqrRecv st_in.spqr msg'.pqRatchet spqrMsgIdx = some (spqr', key) ∧ gamma interpretation S g spqr' = newPqrState ∧
      msg'.mac = computeMac (trMsgKeys pqSalt seed).macKey st_in.peerIk st_in.myIk msg'.wire ∧
      DY.SymEnc.symDec (trMsgKeys pqSalt seed).cipherKey (trMsgKeys pqSalt seed).iv msg'.ciphertext = some ptTerm ∧
      gamma interpretation S g t' = body ∧ gamma interpretation S g ptTerm = pt := by
  obtain ⟨st_s, t_c, coinsLen, hst_s, hpq_eq, hempty, _⟩ := id hAuth
  obtain ⟨t', msg', pqSalt, ptTerm, spqr', key, spqrMsgIdx,
      ht'_rep, hpqSalt_kn, ht'_kn, hparse', hver', hrk', hctr',
      hspqr_step, hspqr'_gam, hmac', hdec', ht'_gam, hpt_gam, _⟩ :=
    authentic_decrypt_witness_of_not_empty_nw
      interpretation hCrypto r₀ S hS g p stateIdx ms₁ recBytes body pt rec st st_in st_prov g_rw
      t₀ msg₀ m rk seed salt newPqrState pqrKey st_s t_c coinsLen
      hrecBytes hrel hspqr_eq hIkEq.1 hIkEq.2 hst hcanon_q htry ht₀ hparse₀ hver₀ hrk₀
      hPeerK hMyK hrecv_spqr hAuth hMacBytes_salt hDecOk_salt hempty hst_s hpq_eq
  exact ⟨t', msg', pqSalt, ptTerm, spqr', key, spqrMsgIdx,
    ht'_rep, hpqSalt_kn, ht'_kn, hparse', hver', hrk', hctr',
    hspqr_step, hspqr'_gam, hmac', hdec', ht'_gam, hpt_gam⟩

/-- Disjunction eliminator for `skipped_decryptWitness` at fixed `(g, t)`. -/
theorem decryptWitness_of_g1_disj_at
    (interpretation : ExternInterpretation) (hCrypto : ExternCryptoLawsHold interpretation)
    (r₀ : ProtocolSetup) (S : SpqrSem) (hS : S = compSemOf interpretation r₀)
    (g : Ghost) (p : Participant) (stateIdx : Nat) (ms₁ : List Move) (evs : List MachineEvent) (sent : List HwBytes)
    (recBytes body pt : HwBytes) (rec : RecordRec) (st st_in st_prov : TRState) (g_rw : RecvWireGhost)
    (t₀ : DY.Bytes) (msg₀ : TRSignalMsg) (m : SignalMessage) (rk seed k_own : DY.Bytes) (newPqrState : HwBytes) (pqrKey : HKDF.Salt)
    {who : List Participant}
    (hmp : MatchedPrefix interpretation r₀ S who g ms₁ evs) (hfit : SrHonestVer.SendsFit evs) (hsent : sent = sentBodies evs)
    (hrecBytes : recBytes = recordBytes rec) (hrel : StateRel interpretation S g st rec) (hspqr_eq : st_in.spqr = st.spqr)
    (hst : ((PersistentLocalState.getLocalState p stateIdx : Traceful TRState).run (runTraceMoves r₀ ms₁)).1 = some st)
    (hcanon_q : TR.Pure.slots_RecordCanonical_Q TR.Pure.slots_NonEmptyV1Q recBytes g_rw.sess) (hpq : PqFromHonest sent body)
    (htry : SignalMessage.tryFrom protoSignalCodec body = .ok m) (ht₀ : t₀ ∈ recvRepresentations interpretation r₀ S g ms₁ body)
    (hparse₀ : parseTrSignalMsg t₀ = some msg₀) (hver₀ : msg₀.version = messageVersion) (hrk₀ : msg₀.ratchetKey = rk)
    (hIkEq : st_prov.peerIk = st_in.peerIk ∧ st_prov.myIk = st_in.myIk)
    (hk_own_gam : gamma interpretation S g k_own = spqrKeyBytes (saltToBytes pqrKey))
    (hMacBytes : body.drop (body.length - 8) = gamma interpretation S g (computeMac (trMsgKeys k_own seed).macKey st_prov.peerIk st_prov.myIk msg₀.wire))
    (hPeerK : st_prov.peerIk.AttackerKnows (runTraceMoves r₀ ms₁)) (hMyK : st_prov.myIk.AttackerKnows (runTraceMoves r₀ ms₁))
    (hDecOk : interpretation aesCbcDecryptSymbol
      [m.ciphertext, gamma interpretation S g (trMsgKeys k_own seed).cipherKey,
       (gamma interpretation S g (trMsgKeys k_own seed).iv).take 16] = some pt)
    (hrecv_spqr : (Symbolic.Swarm.TRREF.SpqrSemOf.spqrModelOf interpretation).recv g_rw.sess.state.pqRatchetState m.pqRatchet = .ok (newPqrState, pqrKey))
    (hDisj : seed.AttackerKnows (runTraceMoves r₀ ms₁) ∨ ∃ salt ∈ honestSalts r₀ ms₁,
      AuthenticDecryptRepB3_g1 interpretation r₀ S g ms₁ body pt t₀ msg₀ st_prov salt seed ∧
      gamma interpretation S g (computeMac (trMsgKeys k_own seed).macKey st_prov.peerIk st_prov.myIk msg₀.wire) =
        gamma interpretation S g (computeMac (trMsgKeys salt seed).macKey st_prov.peerIk st_prov.myIk msg₀.wire) ∧
      interpretation aesCbcDecryptSymbol
        [m.ciphertext, gamma interpretation S g (trMsgKeys salt seed).cipherKey,
         (gamma interpretation S g (trMsgKeys salt seed).iv).take 16] = some pt) :
    ∃ (t' : DY.Bytes) (msg' : TRSignalMsg) (pqSalt ptTerm spqr' key : DY.Bytes) (spqrMsgIdx : UInt32),
      t' ∈ recvRepresentations interpretation r₀ S g ms₁ body ∧ pqSalt.AttackerKnows (runTraceMoves r₀ ms₁) ∧ t'.AttackerKnows (runTraceMoves r₀ ms₁) ∧
      parseTrSignalMsg t' = some msg' ∧ msg'.version = messageVersion ∧ msg'.ratchetKey = rk ∧ msg'.counter = msg₀.counter ∧
      Spqr.spqrRecv st_in.spqr msg'.pqRatchet spqrMsgIdx = some (spqr', key) ∧ gamma interpretation S g spqr' = newPqrState ∧
      msg'.mac = computeMac (trMsgKeys pqSalt seed).macKey st_in.peerIk st_in.myIk msg'.wire ∧
      DY.SymEnc.symDec (trMsgKeys pqSalt seed).cipherKey (trMsgKeys pqSalt seed).iv msg'.ciphertext = some ptTerm ∧
      gamma interpretation S g t' = body ∧ gamma interpretation S g ptTerm = pt :=
  hDisj.elim
    (skipped_decryptWitness_of_seedKnown_at interpretation hCrypto r₀ S hS g p stateIdx ms₁ evs sent
      recBytes body pt rec st st_in st_prov g_rw t₀ msg₀ m rk seed k_own newPqrState pqrKey
      hmp hfit hsent hrecBytes hrel hspqr_eq hst hcanon_q hpq htry ht₀ hparse₀ hver₀ hrk₀ hIkEq hk_own_gam
      hMacBytes hPeerK hMyK hDecOk hrecv_spqr)
    fun ⟨salt, _, hAuth, hMacEq, hDecOk_salt⟩ =>
      skipped_decryptWitness_of_authentic_at interpretation hCrypto r₀ S hS g p stateIdx ms₁
        recBytes body pt rec st st_in st_prov g_rw t₀ msg₀ m rk seed salt newPqrState pqrKey
        hrecBytes hrel hspqr_eq hst hcanon_q htry ht₀ hparse₀ hver₀ hrk₀ hIkEq hPeerK hMyK hrecv_spqr hAuth
        (hMacBytes.trans hMacEq) hDecOk_salt

end Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepAtPure
