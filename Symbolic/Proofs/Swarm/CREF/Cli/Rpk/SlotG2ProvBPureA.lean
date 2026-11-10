/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import DY.Bytes.Basic
import DY.ALaCarte.Basic
import DY.EquationalTheory.DiffieHellman
import Symbolic.Specifications.Model.EquationalTheory.TrWireMsg
import Symbolic.Specifications.Model.EquationalTheory.X25519
public import Symbolic.Proofs.Swarm.CREF.TR.G1.CaseSplit
public import Symbolic.Proofs.Swarm.CREF.TR.G1.HonestSendBranch
public import Symbolic.Proofs.Swarm.CREF.TR.G1.HonestSkelLocal
import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.SymEnc
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.SpinePeelPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.SpinePeelPureA
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.HxplG2W.ProvBAux
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.HxplG2W.SkippedProvBPure
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.HxplG2W.SkippedProvBPureA
import Symbolic.Proofs.Swarm.CREF.TR.G1.G1RepMacTR
import Symbolic.Proofs.Swarm.CREF.TR.G1.NotOpaqueMac
import Symbolic.Proofs.Swarm.CREF.TR.G1.ShapeAddr
import Symbolic.Proofs.Swarm.CREF.TR.PQGamma
import Symbolic.Proofs.Swarm.CREF.TR.RecvDecStepMac
import Symbolic.Proofs.Swarm.CREF.TROpen
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.AcceptNewRecTieAPure -- shake: keep
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepCommonPureA -- shake: keep
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.ALaCarte.Basic

/-!
# Skipped-Key MAC Authenticity and Variant Seed Exposure

Proves attacker-built seed exclusion, MAC case analysis over `whisperTrials`,
authentic decrypt representation or seed exposure, and variant-ratchet-key seed
exposure for logged `TREvent.SkippedKeyStored` seeds.
-/

@[expose] public section

cref_hide_foreign_instances
set_option autoImplicit false

namespace Symbolic.Swarm.CREF.CliPure

cref_open
cref_open_tr

open DY DY.Comparse DY.Literal DY.Libsignal
open DY.Libsignal.HwEvents DY.Libsignal.Rust
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalProtoCodec
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.Composed DY.Libsignal.Composed.Refinement
open DY.Libsignal.TripleRatchet (SessionInfo computeMac hmac messageVersion litByte)
open DY.Libsignal.TripleRatchet (TRState TREvent TRSignalMsg parseTrSignalMsg trMsgKeys)
open DY.Libsignal.Refinement (aesCbcDecryptSymbol ExternCryptoLawsHold)
open Symbolic.Swarm.CREF.TR Symbolic.Swarm.CREF.CliPure.TR
open Symbolic.Swarm.CREF.TR.RecvDec hiding StEntry TREntry TRRecvAllCollide
open Symbolic.Swarm.CREF.TR.RecvDecStep
open Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep hiding StEntry TREntry
open Symbolic.Swarm.CREF.TR.G1

/-- Excludes `G1cOwnKeyCaseB3` for any logged `TREvent.SkippedKeyStored` seed not known to the attacker. -/
theorem attackerBuiltSeed_false_skipped_stage1
    (interpretation : ExternInterpretation) (r₀ : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (g : Ghost) (ms : List Move)
    (t₀ : DY.Bytes) (msg₀ : TRSignalMsg) (s : SessionInfo) (st₀ : TRState)
    (pk mkSeed k_own : DY.Bytes) (rIdx srcIdx skIdx : Nat)
    (hreach : (runTraceMoves r₀ ms).Reachable reachability)
    (hKem32 : TR.G1.Spine.AliceKemLen32 interpretation S g (runTraceMoves r₀ ms))
    (hparse₀ : parseTrSignalMsg t₀ = some msg₀)
    (hlog : (runTraceMoves r₀ ms).EventLoggedAt
      (TREvent.SkippedKeyStored s pk msg₀.counter mkSeed rIdx srcIdx) skIdx)
    (hnk : ¬mkSeed.AttackerKnows (runTraceMoves r₀ ms))
    (hCase : TR.G1.G1cOwnKeyCaseB3 interpretation r₀ S g ms msg₀ st₀ mkSeed k_own) :
    False := by
  obtain ⟨salt₁, inp₀, _hsalt₁, _hgam, hmac₀, hinp_ak, hsh⟩ := hCase
  have hseed_kdf : ∃ ck₁ : DY.Bytes, mkSeed = KdfExtract.kdfExtract ck₁ (litByte 0x01) :=
    exists_kdfCk_of_skippedKeyStored hreach hlog
  obtain ⟨_salt₀, seed₀, _hsalt₀_ak, hseed₀_ak, _hsalt₀_sh, hseed₀_sh, _hprk_memo, hmemo₀⟩ :=
    hmac_wire_attackerKnows_inv_memo_kdf interpretation r₀ S g ms hreach t₀ msg₀ hparse₀
      salt₁ mkSeed st₀.peerIk st₀.myIk inp₀ hseed_kdf hmac₀ hinp_ak hsh
  have hv := spineRkK_and_ikmHolesK (spineRkK_of_skippedKeyStored r₀ ms hreach hlog)
  exact TR.G1.Spine.false_of_oneSidedPeelAK interpretation S g hreach
    (TR.G1.Spine.spineDown_good hreach)
    (fun h => ikmHolesKemK_of_loggedIkmRk interpretation S g hreach hKem32 h)
    (seedSepAK_good_of_reachable interpretation S g hreach hKem32 t₀ mkSeed)
    hv (good_of_skippedKeyStored hreach hlog) hnk hseed₀_ak hmemo₀
    (fun _ he => he) hseed₀_sh

/-- Splits a non-colliding `SkippedKeyStored` MAC match into attacker-known seed,
honest-send match (`G1bHonestSendCaseB3`), or own-key match (`G1cOwnKeyCaseB3`). -/
theorem g1a_case_split_byteSkippedSeed_stage1
    (interpretation : ExternInterpretation)
    (r₀ : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost) (ms : List Move)
    (b : HwBytes) (t₀ : DY.Bytes) (msg₀ : TRSignalMsg)
    (hreach : (runTraceMoves r₀ ms).Reachable reachability)
    (ht₀ : t₀ ∈ recvRepresentations interpretation r₀ S g ms b)
    (hparse₀ : parseTrSignalMsg t₀ = some msg₀)
    (hver₀ : msg₀.version = messageVersion)
    (hNotCol : ¬ RecvCollision interpretation r₀ S g ms t₀)
    (p₀ : Participant) (st₀ : TRState) (hst₀ : st₀ ∈ availableStates r₀ (runTraceMoves r₀ ms))
    (pk mkSeed : DY.Bytes) (rIdx srcIdx skIdx : Nat)
    (hfind₀ : (TripleRatchet.findRecvChain st₀.toDRState.recv pk).isSome = true)
    (hlog : (runTraceMoves r₀ ms).EventLoggedAt
      (TREvent.SkippedKeyStored (st₀.sessionInfo p₀) pk msg₀.counter mkSeed rIdx srcIdx) skIdx)
    (hγ_rk : gamma interpretation S g pk = gamma interpretation S g msg₀.ratchetKey)
    (k_own : DY.Bytes) (hk_own : k_own ∈ ownKeys r₀ (runTraceMoves r₀ ms) st₀ msg₀)
    (hMacBytes : b.drop (b.length - 8) =
      gamma interpretation S g
        (computeMac (trMsgKeys k_own mkSeed).macKey st₀.peerIk st₀.myIk msg₀.wire)) :
    mkSeed.AttackerKnows (runTraceMoves r₀ ms) ∨
    G1bHonestSendCaseB3 interpretation r₀ S g ms msg₀ st₀ mkSeed k_own ∨
    G1cOwnKeyCaseB3 interpretation r₀ S g ms msg₀ st₀ mkSeed k_own := by
  have hno : notOpaqueHeaded msg₀.mac := notOpaqueHeaded_mac_of_parseTrSignalMsg hparse₀
  have hNotMemo := not_memoCollisionOn_of_not_recvCollision interpretation r₀ S g ms t₀ msg₀
    hparse₀ hNotCol
  have hNotOwn := not_ownSaltMacCollision_of_not_recvCollision interpretation r₀ S g ms t₀ msg₀
    hparse₀ hNotCol
  obtain ⟨hns_mac, hpt_mac⟩ :=
    g1_rep_of_recvRepresentations interpretation r₀ S g ms b t₀ msg₀ ht₀ hparse₀
  by_cases hSeedKnows : mkSeed.AttackerKnows (runTraceMoves r₀ ms)
  · exact Or.inl hSeedKnows
  · have ht₀_knows : t₀.AttackerKnows (runTraceMoves r₀ ms) := ht₀.1
    have hmac₀_gamma : gamma interpretation S g msg₀.mac = b.drop (b.length - 8) :=
      (ht₀.2.2.2 msg₀ hparse₀).2.1
    have hmac₀_knows : msg₀.mac.AttackerKnows (runTraceMoves r₀ ms) :=
      attackerKnows_mac_of_parseTrSignalMsg ht₀_knows hparse₀
    let ctx : TrialCtx :=
      { peerIk := st₀.peerIk, myIk := st₀.myIk, extra := [],
        ownSalts := ownKeys r₀ (runTraceMoves r₀ ms) st₀ msg₀, seed? := some mkSeed }
    have hctx : ctx ∈ whisperTrials interpretation r₀ S g (runTraceMoves r₀ ms) msg₀ :=
      Stage1Trials.whisperTrials_mem_of_skippedKeyStored_owner
        hver₀ hst₀ hfind₀ ⟨p₀, rfl⟩ hlog hγ_rk
    have hmac_ctx : gamma interpretation S g
        (computeMac (trMsgKeys k_own mkSeed).macKey ctx.peerIk ctx.myIk msg₀.wire) =
      gamma interpretation S g msg₀.mac := by
      change gamma interpretation S g
        (computeMac (trMsgKeys k_own mkSeed).macKey st₀.peerIk st₀.myIk msg₀.wire) =
        gamma interpretation S g msg₀.mac
      rw [← hMacBytes, hmac₀_gamma]
    obtain ⟨salt₁, hsalt₁, hTripleEq⟩ :=
      Stage1Trials.exists_honestSalt_of_not_ownSaltMacCollision
        hctx rfl hk_own hSeedKnows hmac_ctx hNotOwn
    have hmk_eq : gamma interpretation S g (trMsgKeys salt₁ mkSeed).macKey =
        gamma interpretation S g (trMsgKeys k_own mkSeed).macKey := hTripleEq.2.1
    have hcmac_eq : gamma interpretation S g
        (computeMac (trMsgKeys salt₁ mkSeed).macKey st₀.peerIk st₀.myIk msg₀.wire) =
        gamma interpretation S g
          (computeMac (trMsgKeys k_own mkSeed).macKey st₀.peerIk st₀.myIk msg₀.wire) :=
      gamma_computeMac_congr_macKey interpretation S g _ _ _ _ _ hmk_eq
    have hMacEq : gamma interpretation S g msg₀.mac =
        gamma interpretation S g
          (computeMac (trMsgKeys salt₁ mkSeed).macKey st₀.peerIk st₀.myIk msg₀.wire) :=
      hmac₀_gamma.trans (hMacBytes.trans hcmac_eq.symm)
    have hShMac : (gamma' interpretation S g msg₀.mac).shape =
        (gamma' interpretation S g
          (computeMac (trMsgKeys salt₁ mkSeed).macKey st₀.peerIk st₀.myIk msg₀.wire)).shape :=
      noSelfMemo_skipped interpretation r₀ S g ms t₀ msg₀ hparse₀ hver₀ hns_mac hno hNotMemo
        p₀ st₀ hst₀ salt₁ hsalt₁ pk mkSeed rIdx srcIdx skIdx hfind₀ hγ_rk hlog hpt_mac hMacEq
    let rhsHmac := hmac (trMsgKeys salt₁ mkSeed).macKey
      (Concat.concat st₀.peerIk (Concat.concat st₀.myIk msg₀.wire))
    have hview : DY.Bytes.view? (gamma' interpretation S g msg₀.mac).shape DY.Trunc.Trunc8.SubF =
        some { input := (gamma' interpretation S g rhsHmac).shape } := by
      rw [hShMac]
      unfold DY.Libsignal.TripleRatchet.computeMac
      rw [shape_trunc8_tr]
      exact DY.BytesView.view_pack (SubF := DY.Trunc.Trunc8.SubF) _
    obtain ⟨inp₀, hmac_eq, hshape_eq⟩ :=
      (view?_trunc8_shape_eq_some_iff interpretation S g msg₀.mac
        (gamma' interpretation S g rhsHmac).shape).mp hview
    have hmac_knows : (Trunc.trunc8 inp₀).AttackerKnows (runTraceMoves r₀ ms) := by
      rwa [hmac_eq] at hmac₀_knows
    rcases macKdfSafe_c_trunc8_inv r₀ ms inp₀ hreach hmac_knows with
      hinp_knows | ⟨pqSalt_s, seed_s, myIk_s, peerIk_s, a_s, ns_s, pn_s, m_s, pqMsg_s, hinp_eq⟩
    · exact Or.inr (Or.inr ⟨salt₁, inp₀, hsalt₁, hTripleEq, hmac_eq, hinp_knows, hshape_eq⟩)
    · subst hinp_eq
      exact Or.inr (Or.inl ⟨salt₁, hsalt₁, hTripleEq,
        pqSalt_s, seed_s, myIk_s, peerIk_s, a_s, m_s, pqMsg_s, ns_s, pn_s,
        hmac_eq, hmac_knows, hshape_eq⟩)

theorem recv_mac_authentic_or_seed_known_skipped_stage1
    (interpretation : ExternInterpretation) (hEq : ExternCryptoLawsHold interpretation)
    (r₀ : ProtocolSetup) (S : OpaqueSymbolSemantics) (g' : Ghost) (ms₁ : List Move) (body ptext : HwBytes)
    (m : SignalMessage) (p₀ : Participant) (st₀_src : TRState)
    (t₀ seed k_own : DY.Bytes) (msg₀ : TRSignalMsg) (rIdx srcIdx skIdx : Nat)
    (hIk : TR.G1.AvailableIkShapeId r₀ ms₁)
    (hreach : (runTraceMoves r₀ ms₁).Reachable reachability)
    (hKem32 : TR.G1.Spine.AliceKemLen32 interpretation S g' (runTraceMoves r₀ ms₁))
    (htry : SignalMessage.tryFrom protoSignalCodec body = .ok m)
    (ht₀ : t₀ ∈ recvRepresentations interpretation r₀ S g' ms₁ body)
    (hparse₀ : parseTrSignalMsg t₀ = some msg₀)
    (hver₀ : msg₀.version = messageVersion)
    (hNotCol : ¬RecvCollision interpretation r₀ S g' ms₁ t₀)
    (hst₀_src : st₀_src ∈ availableStates r₀ (runTraceMoves r₀ ms₁))
    (hfind₀ : (TripleRatchet.findRecvChain st₀_src.toDRState.recv msg₀.ratchetKey).isSome = true)
    (hlog : (runTraceMoves r₀ ms₁).EventLoggedAt
      (TREvent.SkippedKeyStored (st₀_src.sessionInfo p₀) msg₀.ratchetKey msg₀.counter seed rIdx srcIdx) skIdx)
    (hk_own : k_own ∈ ownKeys r₀ (runTraceMoves r₀ ms₁) st₀_src msg₀)
    (hMacBytes : body.drop (body.length - 8) =
      gamma interpretation S g' (computeMac (trMsgKeys k_own seed).macKey st₀_src.peerIk st₀_src.myIk msg₀.wire))
    (hDecOk : interpretation aesCbcDecryptSymbol
      [m.ciphertext, gamma interpretation S g' (trMsgKeys k_own seed).cipherKey,
       (gamma interpretation S g' (trMsgKeys k_own seed).iv).take 16] = some ptext) :
    seed.AttackerKnows (runTraceMoves r₀ ms₁) ∨
      TR.G1.AuthenticDecryptRepB3_g1 interpretation r₀ S g' ms₁ body ptext msg₀ st₀_src seed k_own := by
  by_cases hSeedK : seed.AttackerKnows (runTraceMoves r₀ ms₁)
  · exact Or.inl hSeedK
  · right
    rcases g1a_case_split_skippedSeed interpretation r₀ S g' ms₁ body t₀ msg₀
        hreach ht₀ hparse₀ hver₀ hNotCol p₀ st₀_src hst₀_src hfind₀ seed rIdx srcIdx skIdx hlog k_own hk_own hMacBytes with
      hSeedK' | hG1b | hG1c
    · exact False.elim (hSeedK hSeedK')
    · obtain ⟨salt₁, hsalt₁, hTripleEq,
        pqSalt_s, seed_s, myIk_s, peerIk_s, a_s, m_s, pqMsg_s, ns_s, pn_s,
        hmac_eq, htrunc_ak, hsh_inp⟩ := hG1b
      let wire_s := DY.Libsignal.TripleRatchet.trHonestWireMsg (DY.DiffieHellman.dhPk a_s) ns_s pn_s
        (SymEnc.symEnc (trMsgKeys pqSalt_s seed_s).cipherKey (trMsgKeys pqSalt_s seed_s).iv m_s) pqMsg_s
      let inp₀ := DY.Libsignal.TripleRatchet.hmac (trMsgKeys pqSalt_s seed_s).macKey
        (Concat.concat myIk_s (Concat.concat peerIk_s wire_s))
      rcases TR.G1.macKdfSafe_c_trunc8_inv_strong r₀ ms₁ inp₀ hreach htrunc_ak with
        hinp_ak | ⟨pqSalt', seed', myIk', peerIk', a', ns', pn', m', pqMsg', t_s, st_s,
          hinp_eq, hpq_ak, ht'_ak, ha_eq, hst_s, hmyIk_s, hpeerIk_s, hseed_s⟩
      · exact False.elim (attackerBuiltSeed_false_skipped_stage1 interpretation r₀ S g' ms₁
          t₀ msg₀ (st₀_src.sessionInfo p₀) st₀_src msg₀.ratchetKey seed k_own rIdx srcIdx skIdx
          hreach hKem32 hparse₀ hlog hSeedK
          ⟨salt₁, inp₀, hsalt₁, hTripleEq, hmac_eq, hinp_ak, hsh_inp⟩)
      · have hmac_eq' : msg₀.mac =
            computeMac (trMsgKeys pqSalt' seed').macKey myIk' peerIk'
              (DY.Libsignal.TripleRatchet.trHonestWireMsg (DY.DiffieHellman.dhPk a') ns' pn'
                (SymEnc.symEnc (trMsgKeys pqSalt' seed').cipherKey (trMsgKeys pqSalt' seed').iv m')
                pqMsg') := by
          unfold DY.Libsignal.TripleRatchet.computeMac
          rw [← hinp_eq]
          exact hmac_eq
        have hsh_inp' :
            (gamma' interpretation S g'
              (DY.Libsignal.TripleRatchet.hmac (trMsgKeys pqSalt' seed').macKey
                (Concat.concat myIk' (Concat.concat peerIk'
                  (DY.Libsignal.TripleRatchet.trHonestWireMsg (DY.DiffieHellman.dhPk a') ns' pn'
                    (SymEnc.symEnc (trMsgKeys pqSalt' seed').cipherKey (trMsgKeys pqSalt' seed').iv m')
                    pqMsg'))))).shape =
            (gamma' interpretation S g'
              (DY.Libsignal.TripleRatchet.hmac (trMsgKeys salt₁ seed).macKey
                (Concat.concat st₀_src.peerIk (Concat.concat st₀_src.myIk msg₀.wire)))).shape := by
          rw [← hinp_eq]
          exact hsh_inp
        have ht'_kn' :
            (Concat.concat
              (DY.Libsignal.TripleRatchet.trHonestWireMsg (DY.DiffieHellman.dhPk a') ns' pn'
                (SymEnc.symEnc (trMsgKeys pqSalt' seed').cipherKey (trMsgKeys pqSalt' seed').iv m')
                pqMsg')
              msg₀.mac).AttackerKnows (runTraceMoves r₀ ms₁) := by
          rw [hmac_eq]
          exact ht'_ak
        obtain ⟨hpq_sh, hseed_sh, hmyIk_sh, hpeerIk_sh, hwire_sh⟩ :=
          TR.G1.shape_inp_honest_inj interpretation S g' hsh_inp'
        obtain ⟨hrk_sh, hctr_eq, hsh_ct, hsh_pq⟩ :
            (gamma' interpretation S g' (DY.DiffieHellman.dhPk a')).shape =
              (gamma' interpretation S g' msg₀.ratchetKey).shape ∧
            ns' = msg₀.counter ∧
            (gamma' interpretation S g'
              (SymEnc.symEnc (trMsgKeys pqSalt' seed').cipherKey (trMsgKeys pqSalt' seed').iv m')).shape =
              (gamma' interpretation S g' msg₀.ciphertext).shape ∧
            (gamma' interpretation S g' pqMsg').shape =
              (gamma' interpretation S g' msg₀.pqRatchet).shape := by
          unfold parseTrSignalMsg at hparse₀
          cases hsp : Concat.split t₀ (t₀.length - Trunc.trunc8Length) with
          | none => rw [hsp] at hparse₀; cases hparse₀
          | some wm =>
            rcases wm with ⟨w₀, mac₀⟩
            rw [hsp] at hparse₀
            dsimp only [Bind.bind, Option.bind] at hparse₀
            have hvp := DY.Bytes.pack_view? DY.TrWire.TrWireMsg.SubF w₀
            cases hwf : DY.TrWire.trWireMsgFields? w₀ with
            | none => rw [hwf] at hparse₀; cases hparse₀
            | some x₀ =>
              rw [hwf] at hparse₀
              dsimp only [Pure.pure] at hparse₀
              have hview : w₀.view? DY.TrWire.TrWireMsg.SubF = some x₀ := hwf
              rw [hview] at hvp; dsimp only at hvp
              injection hparse₀ with hmsg; subst hmsg
              rw [← hvp] at hwire_sh
              obtain ⟨_, _, hrk, hctr, _, hct, hpq, _⟩ :=
                TR.G1.trWireMsg_shape_eq_imp_addr_eq interpretation interpretation S S g' g'
                  messageVersion (DY.DiffieHellman.dhPk a') ns' pn'
                  (SymEnc.symEnc (trMsgKeys pqSalt' seed').cipherKey (trMsgKeys pqSalt' seed').iv m')
                  pqMsg' DY.TrWire.canonicalVariation
                  x₀.version x₀.senderRatchetKey x₀.counter x₀.previousCounter
                  x₀.ciphertext x₀.pqRatchet x₀.encodingVariation hwire_sh
              exact ⟨hrk, hctr, hct, hpq⟩
        have hrk_eq : DY.DiffieHellman.dhPk a' = msg₀.ratchetKey := by
          rw [ha_eq] at hrk_sh ⊢
          exact TR.G1.eq_dhPk_randTerm32_of_shape_eq interpretation S g' t_s hrk_sh
        have hseed_eq : seed' = seed := by
          rw [← hseed_s] at hseed_sh ⊢
          exact honestSkelUniq_skipped interpretation r₀ S g' ms₁ p₀ st_s st₀_src msg₀ seed
            rIdx srcIdx skIdx hreach hKem32 hst_s hlog hseed_sh
        have hmyIk_eq : myIk' = st₀_src.peerIk := by
          rw [← hmyIk_s] at hmyIk_sh ⊢
          exact TR.G1.eq_of_shape_eq_of_shapeId (hIk st_s hst_s).1 (hIk st₀_src hst₀_src).2 hmyIk_sh
        have hpeerIk_eq : peerIk' = st₀_src.myIk := by
          rw [← hpeerIk_s] at hpeerIk_sh ⊢
          exact TR.G1.eq_of_shape_eq_of_shapeId (hIk st_s hst_s).2 (hIk st₀_src hst₀_src).1 hpeerIk_sh
        have hDecOk_salt₁ : interpretation aesCbcDecryptSymbol
            [m.ciphertext,
             gamma interpretation S g' (trMsgKeys salt₁ seed).cipherKey,
             (gamma interpretation S g' (trMsgKeys salt₁ seed).iv).take 16] = some ptext := by
          rw [hTripleEq.1, hTripleEq.2.2]
          exact hDecOk
        refine ⟨salt₁, hsalt₁, hTripleEq, ?_⟩
        let ct_s := SymEnc.symEnc (trMsgKeys pqSalt' seed').cipherKey (trMsgKeys pqSalt' seed').iv m'
        let wire_s' := DY.Libsignal.TripleRatchet.trHonestWireMsg (DY.DiffieHellman.dhPk a') ns' pn' ct_s pqMsg'
        let t' := Concat.concat wire_s' msg₀.mac
        let msg' : TRSignalMsg :=
          { wire := wire_s'
            mac := msg₀.mac
            version := messageVersion
            ratchetKey := DY.DiffieHellman.dhPk a'
            counter := ns'
            ciphertext := ct_s
            pqRatchet := pqMsg' }
        have hpq_gamma : gamma interpretation S g' pqSalt' = gamma interpretation S g' salt₁ :=
          TR.G1.gamma_eq_of_shape_eq interpretation S g' pqSalt' salt₁ hpq_sh
        have hseed_gamma : gamma interpretation S g' seed' = gamma interpretation S g' seed :=
          TR.G1.gamma_eq_of_shape_eq interpretation S g' seed' seed hseed_sh
        have hwire_gamma_eq : gamma interpretation S g' wire_s' = gamma interpretation S g' msg₀.wire :=
          TR.G1.gamma_eq_of_shape_eq interpretation S g' wire_s' msg₀.wire hwire_sh
        have hver_eq : messageVersion = msg₀.version := hver₀.symm
        have hct_gamma_eq : gamma interpretation S g' ct_s = gamma interpretation S g' msg₀.ciphertext :=
          TR.G1.gamma_eq_of_shape_eq interpretation S g' ct_s msg₀.ciphertext hsh_ct
        have hpqMsg_gamma_eq : gamma interpretation S g' pqMsg' = gamma interpretation S g' msg₀.pqRatchet :=
          TR.G1.gamma_eq_of_shape_eq interpretation S g' pqMsg' msg₀.pqRatchet hsh_pq
        have hrk_gamma_eq : gamma interpretation S g' (DY.DiffieHellman.dhPk a') =
            gamma interpretation S g' msg₀.ratchetKey :=
          TR.G1.gamma_eq_of_shape_eq interpretation S g' (DY.DiffieHellman.dhPk a') msg₀.ratchetKey hrk_sh
        obtain ⟨_, _, _, hmsg₀_prop⟩ := ht₀
        obtain ⟨hwire₀_take, hmac₀_drop, hmac₀_ns, htry₀⟩ := hmsg₀_prop msg₀ hparse₀
        have hwire_take : gamma interpretation S g' wire_s' = body.take (body.length - 8) :=
          hwire_gamma_eq.trans hwire₀_take
        have ht'_gamma : gamma interpretation S g' t' = body := by
          dsimp only [t']
          rw [TR.gamma_concat, hwire_take, hmac₀_drop, List.take_append_drop]
        have hparse' : parseTrSignalMsg t' = some msg' := by
          dsimp only [t', msg']
          rw [hmac_eq']
          exact TR.G1.parseTrSignalMsg_trHonestWireMsg_computeMac (DY.DiffieHellman.dhPk a') ns' pn' ct_s pqMsg'
            (trMsgKeys pqSalt' seed').macKey myIk' peerIk'
        have ht'_mem : t' ∈ recvRepresentations interpretation r₀ S g' ms₁ body := by
          refine ⟨ht'_kn', ht'_gamma, by rw [hparse']; rfl, fun msg hmsg => ?_⟩
          have hmsg_eq : msg = msg' := by rw [hparse'] at hmsg; exact (Option.some.inj hmsg).symm
          subst hmsg_eq
          refine ⟨hwire_take, hmac₀_drop, hmac₀_ns, fun parsed hparsed => ?_⟩
          obtain ⟨hct_m, hrk_m, hpq_m, hctr_m, hver_m⟩ := htry₀ parsed hparsed
          refine ⟨hct_gamma_eq.trans hct_m,
                  hrk_gamma_eq.trans hrk_m,
                  hpqMsg_gamma_eq.trans hpq_m,
                  by dsimp only [msg']; rw [hctr_eq, hctr_m],
                  by dsimp only [msg']; rw [hver_eq, hver_m]⟩
        obtain ⟨hct₀_parsed, _, _, _, _⟩ := htry₀ m htry
        have hct_parsed : gamma interpretation S g' ct_s = m.ciphertext :=
          hct_gamma_eq.trans hct₀_parsed
        have hm_ptext : gamma interpretation S g' m' = ptext :=
          TR.G1.gamma_m_eq_ptext_of_decOk interpretation hEq S g' hpq_gamma hseed_gamma hct_parsed hDecOk_salt₁
        refine ⟨t', msg', m', pqSalt', ht'_mem, ht'_kn', hpq_ak,
          hpq_gamma, ht'_gamma, hparse', hver_eq, hrk_eq, hctr_eq, hpqMsg_gamma_eq, ?_, ?_, hm_ptext⟩
        · dsimp only [msg']
          rw [← hseed_eq, ← hmyIk_eq, ← hpeerIk_eq]
          exact hmac_eq'
        · dsimp only [msg', ct_s]
          rw [← hseed_eq]
          exact DY.SymEnc.symDec_symEnc _ _ _
    · exact False.elim (attackerBuiltSeed_false_skipped_stage1 interpretation r₀ S g' ms₁
        t₀ msg₀ (st₀_src.sessionInfo p₀) st₀_src msg₀.ratchetKey seed k_own rIdx srcIdx skIdx
        hreach hKem32 hparse₀ hlog hSeedK hG1c)

/-- When `msg₀.ratchetKey` is an X25519 variant on a `SkippedKeyStored` trial, `seed` is attacker-known. -/
theorem slotG2_seed_known_of_provB_variant_stage1
    (interpretation : ExternInterpretation)
    (r₀ : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost) (ms : List Move)
    (body : HwBytes) (t₀ : DY.Bytes) (msg₀ : TRSignalMsg) (p_src : Participant) (st_src : TRState)
    (pk seed k_own : DY.Bytes) (rIdx srcIdx skIdx : Nat) (y : DY.X25519.Variant.SubF DY.Bytes)
    (hreach : (runTraceMoves r₀ ms).Reachable reachability)
    (hKem32 : TR.G1.Spine.AliceKemLen32 interpretation S g (runTraceMoves r₀ ms))
    (ht₀ : t₀ ∈ recvRepresentations interpretation r₀ S g ms body)
    (hparse₀ : parseTrSignalMsg t₀ = some msg₀) (hver₀ : msg₀.version = messageVersion)
    (hNotCol : ¬RecvCollision interpretation r₀ S g ms t₀)
    (hst_src : st_src ∈ availableStates r₀ (runTraceMoves r₀ ms))
    (hfind_src : (TripleRatchet.findRecvChain st_src.toDRState.recv pk).isSome = true)
    (hlog : (runTraceMoves r₀ ms).EventLoggedAt
      (TREvent.SkippedKeyStored (st_src.sessionInfo p_src) pk msg₀.counter seed rIdx srcIdx) skIdx)
    (hγ_rk : gamma interpretation S g pk = gamma interpretation S g msg₀.ratchetKey)
    (hk_own : k_own ∈ ownKeys r₀ (runTraceMoves r₀ ms) st_src msg₀)
    (hMacBytes : body.drop (body.length - 8) =
      gamma interpretation S g (computeMac (trMsgKeys k_own seed).macKey st_src.peerIk st_src.myIk msg₀.wire))
    (hVar₀ : msg₀.ratchetKey.view? DY.X25519.Variant.SubF = some y) :
    seed.AttackerKnows (runTraceMoves r₀ ms) := by
  by_cases hSeedK : seed.AttackerKnows (runTraceMoves r₀ ms)
  · exact hSeedK
  · rcases g1a_case_split_byteSkippedSeed_stage1 interpretation r₀ S g ms body t₀ msg₀
        hreach ht₀ hparse₀ hver₀ hNotCol p_src st_src hst_src pk seed rIdx srcIdx skIdx hfind_src
        hlog hγ_rk k_own hk_own hMacBytes with hSeedK' | hG1b | hG1c
    · exact hSeedK'
    · obtain ⟨salt₁, hsalt₁, hTripleEq, pqSalt_s, seed_s, myIk_s, peerIk_s, a_s, m_s, pqMsg_s, ns_s, pn_s,
        hmac_eq, htrunc_ak, hsh_inp⟩ := hG1b
      let wire_s := DY.Libsignal.TripleRatchet.trHonestWireMsg (DY.DiffieHellman.dhPk a_s) ns_s pn_s
        (SymEnc.symEnc (trMsgKeys pqSalt_s seed_s).cipherKey (trMsgKeys pqSalt_s seed_s).iv m_s) pqMsg_s
      let inp₀ := DY.Libsignal.TripleRatchet.hmac (trMsgKeys pqSalt_s seed_s).macKey
        (Concat.concat myIk_s (Concat.concat peerIk_s wire_s))
      rcases TR.G1.macKdfSafe_c_trunc8_inv_strong r₀ ms inp₀ hreach htrunc_ak with
        hinp_ak | ⟨pqSalt', seed', myIk', peerIk', a', ns', pn', m', pqMsg', t_s, _st_s,
          hinp_eq, _hpq_ak, _ht'_ak, ha_eq, _hst_s, _hmyIk_s, _hpeerIk_s, _hseed_s⟩
      · exact False.elim (attackerBuiltSeed_false_skipped_stage1 interpretation r₀ S g ms
          t₀ msg₀ (st_src.sessionInfo p_src) st_src pk seed k_own rIdx srcIdx skIdx
          hreach hKem32 hparse₀ hlog hSeedK
          ⟨salt₁, inp₀, hsalt₁, hTripleEq, hmac_eq, hinp_ak, hsh_inp⟩)
      · have hsh_inp' :
            (gamma' interpretation S g
              (DY.Libsignal.TripleRatchet.hmac (trMsgKeys pqSalt' seed').macKey
                (Concat.concat myIk' (Concat.concat peerIk'
                  (DY.Libsignal.TripleRatchet.trHonestWireMsg (DY.DiffieHellman.dhPk a') ns' pn'
                    (SymEnc.symEnc (trMsgKeys pqSalt' seed').cipherKey (trMsgKeys pqSalt' seed').iv m') pqMsg'))))).shape =
            (gamma' interpretation S g
              (DY.Libsignal.TripleRatchet.hmac (trMsgKeys salt₁ seed).macKey
                (Concat.concat st_src.peerIk (Concat.concat st_src.myIk msg₀.wire)))).shape := by
          rw [← hinp_eq]; exact hsh_inp
        obtain ⟨_hpq_sh, _hseed_sh, _hmyIk_sh, _hpeerIk_sh, hwire_sh⟩ :=
          TR.G1.shape_inp_honest_inj interpretation S g hsh_inp'
        have hrk_sh :
            (gamma' interpretation S g (DY.DiffieHellman.dhPk a')).shape =
            (gamma' interpretation S g msg₀.ratchetKey).shape := by
          unfold parseTrSignalMsg at hparse₀
          cases hsp : Concat.split t₀ (t₀.length - Trunc.trunc8Length) with
          | none => rw [hsp] at hparse₀; cases hparse₀
          | some wm =>
            rcases wm with ⟨w₀, mac₀⟩
            rw [hsp] at hparse₀
            dsimp only [Bind.bind, Option.bind] at hparse₀
            have hvp := DY.Bytes.pack_view? DY.TrWire.TrWireMsg.SubF w₀
            cases hwf : DY.TrWire.trWireMsgFields? w₀ with
            | none => rw [hwf] at hparse₀; cases hparse₀
            | some x₀ =>
              rw [hwf] at hparse₀
              dsimp only [Pure.pure] at hparse₀
              have hview : w₀.view? DY.TrWire.TrWireMsg.SubF = some x₀ := hwf
              rw [hview] at hvp; dsimp only at hvp
              injection hparse₀ with hmsg; subst hmsg
              rw [← hvp] at hwire_sh
              exact (TR.G1.trWireMsg_shape_eq_imp_addr_eq interpretation interpretation S S g g
                messageVersion (DY.DiffieHellman.dhPk a') ns' pn'
                (SymEnc.symEnc (trMsgKeys pqSalt' seed').cipherKey (trMsgKeys pqSalt' seed').iv m')
                pqMsg' DY.TrWire.canonicalVariation
                x₀.version x₀.senderRatchetKey x₀.counter x₀.previousCounter
                x₀.ciphertext x₀.pqRatchet x₀.encodingVariation hwire_sh).2.2.1
        have hrk_eq : DY.DiffieHellman.dhPk a' = msg₀.ratchetKey := by
          rw [ha_eq] at hrk_sh ⊢; exact TR.G1.eq_dhPk_randTerm32_of_shape_eq interpretation S g t_s hrk_sh
        have hvnone : (DY.DiffieHellman.dhPk a').view? DY.X25519.Variant.SubF = none :=
          Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _
        rw [← hrk_eq, hvnone] at hVar₀; nomatch hVar₀
    · exact False.elim (attackerBuiltSeed_false_skipped_stage1 interpretation r₀ S g ms
        t₀ msg₀ (st_src.sessionInfo p_src) st_src pk seed k_own rIdx srcIdx skIdx
        hreach hKem32 hparse₀ hlog hSeedK hG1c)

end Symbolic.Swarm.CREF.CliPure
