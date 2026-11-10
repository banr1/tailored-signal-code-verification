/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvAtFactsPure
public import Symbolic.Proofs.Swarm.CREF.RecvWire.SkippedNotJunkFixPure
public import Symbolic.Proofs.Swarm.CREF.RecvWire.SlotG2HelpersPure
public import Symbolic.Proofs.Swarm.CREF.TR.RecvDecStepSkippedG1AtPureA
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.HxplG2W.SupplyVck
import Symbolic.Proofs.Swarm.CREF.RecvWire.SkippedProvBPureA
import Symbolic.Proofs.Swarm.CREF.RecvWire.SlotG2ProvBPureA
import Symbolic.Proofs.Swarm.CREF.RecvWire.SpinePeelPure
import Symbolic.Proofs.Swarm.CREF.TR.FreshSigma
import Symbolic.Proofs.Swarm.CREF.TR.G1.CanonLocal
import Symbolic.Proofs.Swarm.CREF.TR.G1.HonestSpineRk
import Symbolic.Proofs.Swarm.CREF.TR.RecvDecStepSkippedProvTR
import Symbolic.Proofs.Swarm.CREF.TR.SkippedVarLit
import Symbolic.Proofs.Swarm.CREF.TR.VarRecvSeedKnown
import Symbolic.Proofs.Swarm.CREF.TROpen
import Symbolic.Proofs.Swarm.TRREF.GrowthRecvPure.BranchesBPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepCommonPureA -- shake: keep
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepRatchetDHProvPure -- shake: keep
public import Symbolic.Proofs.Swarm.CREF.TR.RecvCol -- shake: keep

/-!
# Skipped-Key `ProvB` Dispatch for `RecvWire`

Proves `slotG2_skipped_provB_dispatch_at`, `rcv_honestSkelUniq_of_matchedPrefix`, and
`skipped_pk_dispatch_atK'` for skipped-key Whisper decryption.
-/

@[expose] public section

cref_hide_foreign_instances
set_option autoImplicit false

namespace Symbolic.Swarm.CREF.CliPureRcv.RecvWirePure
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure Symbolic.Swarm.CREF.CliPureRcv
open Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepAtPure
open DY.Libsignal.Composed.Refinement.Cli (ExternContractsHoldCli)

cref_open
cref_open_tr

open DY DY.Comparse DY.Literal DY.Libsignal
open DY.Libsignal.HwEvents DY.Libsignal.Rust
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalProtoCodec
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.Composed DY.Libsignal.Composed.Refinement
open DY.Libsignal.TripleRatchet (RecvChain findRecvChain recvChainFor consumeMessageKey computeMac
  messageVersion)
open DY.Libsignal.TripleRatchet (TRState TREvent TRSignalMsg parseTrSignalMsg trMsgKeys)
open DY.Libsignal.Refinement (aesCbcDecryptSymbol ExternCryptoLawsHold)
open Symbolic.Swarm.CREF.TR Symbolic.Swarm.CREF.CliPure.TR Symbolic.Swarm.CREF.CliPureRcv.TR
open Symbolic.Swarm.CREF.TR.RecvDec hiding StEntry TREntry TRRecvAllCollide
open Symbolic.Swarm.CREF.TR.RecvDecStep
open Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep hiding StEntry TREntry
open Symbolic.Swarm.CREF.CliPure.TR.RecvDecStepAt
open Symbolic.Swarm.CREF.TR.G1

/-- Dispatches the `ProvB` skipped-key provenance branch into attacker seed knowledge or `AuthenticDecryptRepB3_g1`. -/
theorem slotG2_skipped_provB_dispatch_at {interpretation : ExternInterpretation}
    (hEq : DY.Libsignal.Refinement.ExternCryptoLawsHold interpretation)
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {who : List Participant} {g : Ghost} {ms : List Move} {τ₁ : List MachineEvent}
    (p p_src : Participant) (body ptBytes : HwBytes) (m : SignalMessage) (st₀ st_src : TRState)
    (c₀ : RecvChain) (t₀ pk seed k_own : DY.Bytes) (msg₀ : TRSignalMsg) (rIdx srcIdx skIdx : Nat)
    (hmp : MatchedPrefix interpretation r S who g ms τ₁) (hat : RecvAtFacts interpretation r S g ms)
    (htry : SignalMessage.tryFrom protoSignalCodec body = .ok m)
    (ht₀ : t₀ ∈ recvRepresentations interpretation r S g ms body) (hparse₀ : parseTrSignalMsg t₀ = some msg₀)
    (hver₀ : msg₀.version = messageVersion) (hctr₀ : msg₀.counter = UInt32.ofBitVec m.counter)
    (hNotCol : ¬RecvCollision interpretation r S g ms t₀)
    (_hst_src_at : TR.G1.TRStateStoredAt p_src st_src srcIdx (runTraceMoves r ms))
    (hst_src : st_src ∈ availableStates r (runTraceMoves r ms))
    (hsinfo_eq : st_src.sessionInfo p_src = st₀.sessionInfo p) (_hinit : st_src.initiator = false)
    (hc₀_mem : c₀ ∈ st_src.recv) (hc₀_rk : c₀.ratchetKey = pk) (_hc₀_rIdx : c₀.rIdx = rIdx) (_hlt : msg₀.counter < c₀.index)
    (hk_own : k_own ∈ ownKeys r (runTraceMoves r ms) st_src msg₀)
    (hlog : (runTraceMoves r ms).EventLoggedAt (TREvent.SkippedKeyStored (st₀.sessionInfo p) pk (UInt32.ofBitVec m.counter) seed rIdx srcIdx) skIdx)
    (hIW : TR.G1.InstallWitnessTR r (runTraceMoves r ms)) (hγ_pk : gamma interpretation S g pk = m.senderRatchetKey.bytes.toList)
    (hMacBytes : body.drop (body.length - 8) = gamma interpretation S g (computeMac (trMsgKeys k_own seed).macKey st_src.peerIk st_src.myIk msg₀.wire))
    (hPeerK : st_src.peerIk.AttackerKnows (runTraceMoves r ms)) (hMyK : st_src.myIk.AttackerKnows (runTraceMoves r ms))
    (hDecOk : interpretation aesCbcDecryptSymbol
      [m.ciphertext, gamma interpretation S g (trMsgKeys k_own seed).cipherKey, (gamma interpretation S g (trMsgKeys k_own seed).iv).take 16] = some ptBytes) :
    ∃ (t₁ : DY.Bytes) (msg₁ : TRSignalMsg),
      t₁ ∈ recvRepresentations interpretation r S g ms body ∧ parseTrSignalMsg t₁ = some msg₁ ∧
      msg₁.version = messageVersion ∧ msg₁.ratchetKey = pk ∧ msg₁.counter = msg₀.counter ∧
      body.drop (body.length - 8) = gamma interpretation S g (computeMac (trMsgKeys k_own seed).macKey st_src.peerIk st_src.myIk msg₁.wire) ∧
      (seed.AttackerKnows (runTraceMoves r ms) ∨ ∃ salt ∈ honestSalts r ms,
        AuthenticDecryptRepB3_g1 interpretation r S g ms body ptBytes t₁ msg₁ st_src salt seed ∧
        gamma interpretation S g (computeMac (trMsgKeys k_own seed).macKey st_src.peerIk st_src.myIk msg₁.wire) =
          gamma interpretation S g (computeMac (trMsgKeys salt seed).macKey st_src.peerIk st_src.myIk msg₁.wire) ∧
        interpretation aesCbcDecryptSymbol [m.ciphertext, gamma interpretation S g (trMsgKeys salt seed).cipherKey,
          (gamma interpretation S g (trMsgKeys salt seed).iv).take 16] = some ptBytes) := by
  have hreach : (runTraceMoves r ms).Reachable reachability := hmp.2.1.2.2.1.1
  have hKem32 := TR.G1.Spine.aliceKemLen32_of_matchedPrefix hmp
  have hIk : TR.G1.AvailableIkShapeId r ms := TR.G1.Ik.availableIkShapeId_all r ms
  have hHist : TR.G1.RecvHistInvTR interpretation S g r ms := hat.hist
  have hNotLow : DY.X25519.isLowOrderKey ((gamma interpretation S g pk).map BitVec.toNat) = false := by
    rw [← hc₀_rk]; exact hat.notLow st_src hst_src c₀ hc₀_mem
  have hrkK : pk.AttackerKnows (runTraceMoves r ms) := pk_attackerKnows_of_skippedKeyStored hreach hlog
  have hγ_msg₀ : gamma interpretation S g msg₀.ratchetKey = gamma interpretation S g pk :=
    (((ht₀.2.2.2 msg₀ hparse₀).2.2.2 m htry).2.1).trans hγ_pk.symm
  have hlog_src : (runTraceMoves r ms).EventLoggedAt
      (TREvent.SkippedKeyStored (st_src.sessionInfo p_src) pk msg₀.counter seed rIdx srcIdx) skIdx := by
    rw [hsinfo_eq, hctr₀]; exact hlog
  have hfind_src : (TripleRatchet.findRecvChain st_src.toDRState.recv pk).isSome = true :=
    List.find?_isSome.mpr ⟨c₀, hc₀_mem, beq_iff_eq.mpr hc₀_rk⟩
  have hConcl : TR.RecvDecStep.SkippedVarKnownCk.SkippedVarConcl interpretation r S g ms body ptBytes m st_src pk seed k_own := by
    by_cases hJunk : TR.G1.JunkTR pk
    · exact skippedVar_of_litJunk' interpretation hEq r S g ms body ptBytes m st_src
        t₀ pk seed k_own msg₀ hreach htry ht₀ hparse₀ hver₀ hctr₀ hlog hJunk hγ_pk hMacBytes hPeerK hMyK
    have hCaseA' : TR.G1.CaseA' pk := Classical.byContradiction fun hNotA => hJunk (TR.G1.junkTR_of_caseB' hNotA)
    by_cases hrk_eq : msg₀.ratchetKey = pk
    · have hlog_rk : (runTraceMoves r ms).EventLoggedAt
          (TREvent.SkippedKeyStored (st_src.sessionInfo p_src) msg₀.ratchetKey msg₀.counter seed rIdx srcIdx) skIdx := by
        rw [hrk_eq]; exact hlog_src
      have hDisj₀ := recv_mac_authentic_or_seed_known_skipped_stage1 interpretation hEq r S g ms body ptBytes m p_src st_src
        t₀ seed k_own msg₀ rIdx srcIdx skIdx hIk hreach hKem32 htry ht₀ hparse₀ hver₀ hNotCol
        hst_src (hrk_eq.symm ▸ hfind_src) hlog_rk hk_own hMacBytes hDecOk
      exact ⟨t₀, msg₀, ht₀, hparse₀, hver₀, hrk_eq, hctr₀, hMacBytes, hDisj₀⟩
    · cases hVar : pk.view? DY.X25519.Variant.SubF with
      | none =>
        have hγ₁ : gamma interpretation S g msg₀.ratchetKey = gamma interpretation S g c₀.ratchetKey := by
          rw [hc₀_rk]; exact hγ_msg₀
        exact absurd ((TR.G1.rk_eq_of_noncolliding_caseA' interpretation hEq r S g ms hHist hIW
          hst_src hc₀_mem (hc₀_rk.symm ▸ hCaseA') (hc₀_rk.symm ▸ hVar) hparse₀ hver₀ hγ₁ hNotCol).trans hc₀_rk) hrk_eq
      | some x =>
        by_cases hbase : DY.X25519.normalizeX25519Key msg₀.ratchetKey = DY.X25519.normalizeX25519Key pk
        · cases hVar₀ : msg₀.ratchetKey.view? DY.X25519.Variant.SubF with
          | none =>
            exact absurd (⟨hc₀_rk.symm ▸ hbase, hVar₀⟩ :
                DY.X25519.normalizeX25519Key msg₀.ratchetKey = DY.X25519.normalizeX25519Key c₀.ratchetKey ∧
                msg₀.ratchetKey.view? DY.X25519.Variant.SubF = none) fun hPB =>
              RecvPrekeyProm.HxplG2W.false_of_noRatchet_sameBase_dhPk_pkd interpretation hEq r S g ms
                body m st_src c₀ t₀ msg₀ x htry ht₀ hparse₀ hNotCol hst_src hc₀_mem
                (hc₀_rk.symm ▸ hCaseA') (hc₀_rk.symm ▸ hVar) (hc₀_rk.symm ▸ hrk_eq) (hc₀_rk.symm ▸ hγ_pk) hPB.1 hPB.2
          | some y =>
            have hSeedK := slotG2_seed_known_of_provB_variant_stage1 interpretation r S g ms body t₀ msg₀
              p_src st_src pk seed k_own rIdx srcIdx skIdx y hreach hKem32 ht₀ hparse₀ hver₀ hNotCol
              hst_src hfind_src hlog_src hγ_msg₀.symm hk_own hMacBytes hVar₀
            exact skippedVar_of_seedKnown' interpretation hEq r S g ms body ptBytes m st_src
              t₀ pk seed k_own msg₀ htry ht₀ hparse₀ hver₀ hctr₀ hrkK hSeedK hγ_pk hMacBytes hPeerK hMyK
        · exact (Symbolic.Swarm.CREF.TR.RecvDecStep.SkippedVarLit.false_of_skippedVar_diffBase
            interpretation hEq r S g ms body m st_src c₀ t₀ pk msg₀ ht₀ hparse₀ hver₀ htry hNotCol
            hst_src hc₀_mem hc₀_rk hCaseA' hrk_eq hHist hIW hγ_pk hbase hNotLow).elim
  obtain ⟨t₁, msg₁, ht₁, hparse₁, hver₁, hrk₁, hctr₁, hMacBytes₁, hDisj₁⟩ := hConcl
  obtain ⟨t₂, msg₂, ht₂, hparse₂, hver₂, hrk₂, hctr₂, hMacBytes₂, hOut⟩ :=
    g1_disj_to_salt_form_at interpretation r S g ms body ptBytes m st_src
      t₁ pk seed k_own msg₁ hreach (exists_kdfCk_of_skippedKeyStored hreach hlog) ht₁ hparse₁ hver₁ hrk₁ hMacBytes₁ hDecOk hDisj₁
  exact ⟨t₂, msg₂, ht₂, hparse₂, hver₂, hrk₂, hctr₂.trans (hctr₁.trans hctr₀.symm), hMacBytes₂, hOut⟩

theorem rcv_honestSkelUniq_of_matchedPrefix
    {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {g : Ghost} {ms : List Move} {τ : List MachineEvent}
    (hmp : MatchedPrefix interpretation r S who g ms τ) :
    TR.G1.HonestSkelUniq interpretation r S g ms := by
  intro st_s hst_s st₀ hst₀ msg₀ mkSeed _hrk hseed hshape
  have hT : TR.G1.ReachableTrace (runTraceMoves r ms) := hmp.2.1.2.2.1.1
  have hKem32 := TR.G1.Spine.aliceKemLen32_of_matchedPrefix hmp
  exact TR.G1.SkelLocal.seed_eq_of_holes interpretation r S g ms hst_s hst₀ hseed
    (fun d₁ d₂ hP hd₁ _ _ =>
      TR.G1.Spine.hdh_of_spineRk interpretation S g
        (TR.G1.Spine.ikAt_spkAt_false (runTraceMoves r ms))
        (TR.G1.Spine.ekAt_ikAt_false (runTraceMoves r ms))
        (TR.G1.Spine.ekAt_spkAt_false (runTraceMoves r ms))
        (TR.G1.Spine.ekAt_opkAt_false (runTraceMoves r ms))
        (fun _ _ h => TR.G1.Spine.loggedIkmRk_roleHoles h)
        rfl
        (TR.G1.Spine.spineRk_send_runTrace hst_s)
        (TR.G1.Spine.spineRk_recvSeed_runTrace hst₀ hseed)
        hshape d₁ d₂ hP hd₁)
    (TR.G1.Spine.kemCanonPeel_of_aliceKemLen32 interpretation S g hT hKem32 _ _)
    hshape

theorem skippedVar_of_fresh_sameBase_variant_ex
    (interpretation : ExternInterpretation) (hEq : ExternCryptoLawsHold interpretation)
    (r₀ : ProtocolSetup) (S : OpaqueSymbolSemantics) (g' : Ghost) (ms₁ : List Move) (body ptext : HwBytes) (m : SignalMessage)
    (st₀_src : TRState) (c₀ c₀' : RecvChain) (t₀ pk seed k_own : DY.Bytes)
    (msg₀ : TRSignalMsg) (y : DY.X25519.Variant.SubF DY.Bytes)
    (hSkel : TR.G1.HonestSkelUniq interpretation r₀ S g' ms₁)
    (hABS' : TR.G1.G1cAttackerBuiltSeedExcl' interpretation r₀ S g' ms₁)
    (hreach : (runTraceMoves r₀ ms₁).Reachable reachability)
    (htry : SignalMessage.tryFrom protoSignalCodec body = .ok m)
    (ht₀ : t₀ ∈ recvRepresentations interpretation r₀ S g' ms₁ body) (hparse₀ : parseTrSignalMsg t₀ = some msg₀)
    (hver₀ : msg₀.version = messageVersion) (hctr₀ : msg₀.counter = UInt32.ofBitVec m.counter)
    (hNotCol : ¬RecvCollision interpretation r₀ S g' ms₁ t₀)
    (hst₀_src : st₀_src ∈ availableStates r₀ (runTraceMoves r₀ ms₁))
    (hrcf : recvChainFor st₀_src.toDRState pk = some (c₀, true))
    (hcons : consumeMessageKey c₀ (UInt32.ofBitVec m.counter) = some (seed, c₀'))
    (hk_own : k_own ∈ ownKeys r₀ (runTraceMoves r₀ ms₁) st₀_src msg₀) (hrkK : pk.AttackerKnows (runTraceMoves r₀ ms₁))
    (hγ_pk : gamma interpretation S g' pk = m.senderRatchetKey.bytes.toList)
    (hMacBytes : body.drop (body.length - 8) =
      gamma interpretation S g' (computeMac (trMsgKeys k_own seed).macKey st₀_src.peerIk st₀_src.myIk msg₀.wire))
    (hPeerK : st₀_src.peerIk.AttackerKnows (runTraceMoves r₀ ms₁)) (hMyK : st₀_src.myIk.AttackerKnows (runTraceMoves r₀ ms₁))
    (hDecOk : interpretation aesCbcDecryptSymbol
      [m.ciphertext, gamma interpretation S g' (trMsgKeys k_own seed).cipherKey,
       (gamma interpretation S g' (trMsgKeys k_own seed).iv).take 16] = some ptext)
    (hbase : DY.X25519.normalizeX25519Key msg₀.ratchetKey = DY.X25519.normalizeX25519Key pk)
    (hfind : findRecvChain st₀_src.recv msg₀.ratchetKey = none)
    (hVar₀ : msg₀.ratchetKey.view? DY.X25519.Variant.SubF = some y) :
    TR.RecvDecStep.SkippedVarKnownCk.SkippedVarConcl interpretation r₀ S g' ms₁ body ptext m st₀_src pk seed k_own := by
  obtain ⟨hseed₀, ck, hseed_kdf⟩ := recvSeed_eq_some_of_fresh_sameBase' hver₀ hctr₀ hrcf hcons hbase hfind
  have hDisj₀ := rcv_g1_authentic_or_seed_known
    interpretation hEq r₀ S g' ms₁ body ptext m hSkel hABS' hreach
    htry t₀ msg₀ ht₀ hparse₀ hNotCol st₀_src hst₀_src seed hseed₀ k_own hk_own hMacBytes hDecOk
  have hSeedK : seed.AttackerKnows (runTraceMoves r₀ ms₁) := by
    rcases hDisj₀ with hSeedK | ⟨salt₁, _hsalt₁, _hTripleEq, hAuth⟩
    · exact hSeedK
    · obtain ⟨t', msg', _ptTerm, pqSalt, _ht'_mem, ht'_ak, _hpq_ak, _hpq_gam, _ht'_gam,
        hparse', _hver_eq, hrk_eq, _hcnt_eq, _hpq_eq, hmac_eq, _hdec, _hpt_gam⟩ := hAuth
      rw [hseed_kdf] at hmac_eq ⊢
      exact TR.G1.seed_known_of_forgedMac_variant_tr hreach ht'_ak hparse' hmac_eq (hrk_eq.symm ▸ hVar₀)
  obtain ⟨t₁, msg₁, ht₁_rep, hparse₁, hver₁, hrk₁, hctr₁, hMacBytes₁⟩ :=
    Symbolic.Swarm.CREF.TR.RecvDecStep.SkippedVarKnownCk.svk_rk_switch_of_seedKnown
      interpretation hEq r₀ S g' ms₁ body m htry ht₀ hparse₀ hrkK hSeedK hMacBytes hPeerK hMyK hγ_pk
  exact ⟨t₁, msg₁, ht₁_rep, hparse₁, hver₁.trans hver₀, hrk₁, hctr₁.trans hctr₀, hMacBytes₁, Or.inl hSeedK⟩

theorem snjf_skippedVarConcl'
    {interpretation : ExternInterpretation} (hext : ExternContractsHoldCli interpretation)
    {r : ProtocolSetup} (hwf : ProtocolSetupWF r) {S : OpaqueSymbolSemantics} {who : List Participant} {ok : Nat → Bool}
    {g : Ghost} {ms : List Move} {acc : List MachineEvent} (hc : CleanBy interpretation r S who ok g ms acc)
    (hNJ : RcvSkippedNotJunkSeedProvAt interpretation r S g ms)
    (hRes : RcvByteChainReselectAt interpretation r S g ms acc)
    (p : Participant) (body ptBytes : HwBytes) (m : SignalMessage) (st₀ st_prov : TRState)
    (t₀ pk seed k_own : DY.Bytes) (msg₀ : TRSignalMsg) (rIdx srcIdx skIdx : Nat)
    (htry : SignalMessage.tryFrom protoSignalCodec body = .ok m)
    (ht₀ : t₀ ∈ recvRepresentations interpretation r S g ms body) (hparse₀ : parseTrSignalMsg t₀ = some msg₀)
    (hver₀ : msg₀.version = messageVersion) (hctr₀ : msg₀.counter = UInt32.ofBitVec m.counter)
    (hNotCol : ¬RecvCollision interpretation r S g ms t₀) (hNotRS : ¬ReselectCollision interpretation r S g ms t₀)
    (hst_prov : st_prov ∈ availableStates r (runTraceMoves r ms))
    (hseed_pk : ∀ msg, msg.version = messageVersion → msg.ratchetKey = pk →
      msg.counter = msg₀.counter → recvSeed st_prov msg = some seed)
    (hk_own : k_own ∈ ownKeys r (runTraceMoves r ms) st_prov msg₀)
    (hlog : (runTraceMoves r ms).EventLoggedAt
      (TREvent.SkippedKeyStored (st₀.sessionInfo p) pk (UInt32.ofBitVec m.counter) seed rIdx srcIdx) skIdx)
    (hHist : TR.G1.RecvHistInvTR interpretation S g r ms) (hIW : TR.G1.InstallWitnessTR r (runTraceMoves r ms))
    (hγ_pk : gamma interpretation S g pk = m.senderRatchetKey.bytes.toList)
    (hMacBytes : body.drop (body.length - 8) =
      gamma interpretation S g (computeMac (trMsgKeys k_own seed).macKey st_prov.peerIk st_prov.myIk msg₀.wire))
    (hPeerK : st_prov.peerIk.AttackerKnows (runTraceMoves r ms)) (hMyK : st_prov.myIk.AttackerKnows (runTraceMoves r ms))
    (hDecOk : interpretation aesCbcDecryptSymbol
      [m.ciphertext, gamma interpretation S g (trMsgKeys k_own seed).cipherKey,
       (gamma interpretation S g (trMsgKeys k_own seed).iv).take 16] = some ptBytes)
    (hAliasLoc : ∀ (c₀ c_ex : RecvChain), recvChainFor st_prov.toDRState pk = some (c₀, true) →
      findRecvChain st_prov.recv msg₀.ratchetKey = some c_ex → msg₀.ratchetKey ≠ pk → ¬TR.G1.JunkTR pk →
      (∃ x, pk.view? DY.X25519.Variant.SubF = some x) →
      pk.AttackerKnows (runTraceMoves r ms) → ¬seed.AttackerKnows (runTraceMoves r ms) → False) :
    TR.RecvDecStep.SkippedVarKnownCk.SkippedVarConcl interpretation r S g ms body ptBytes m st_prov pk seed k_own := by
  have hEq : ExternCryptoLawsHold interpretation := hext.1
  have hRun : ModelRun r ms := hc.matched.2.1; have hreach : (runTraceMoves r ms).Reachable reachability := hRun.2.2.1.1
  have hSkel := rcv_honestSkelUniq_of_matchedPrefix hc.matched
  have hABS' := rcv_abs_of_matchedPrefix hc.matched
  by_cases hJunk : TR.G1.JunkTR pk
  · exact skippedVar_of_litJunk' interpretation hEq r S g ms body ptBytes m st_prov
      t₀ pk seed k_own msg₀ hreach htry ht₀ hparse₀ hver₀ hctr₀ hlog hJunk hγ_pk hMacBytes hPeerK hMyK
  have hCaseA' : TR.G1.CaseA' pk := Classical.byContradiction fun hNotA => hJunk (TR.G1.junkTR_of_caseB' hNotA)
  have hseed_m : ∀ msg, msg.version = messageVersion → msg.ratchetKey = pk →
      msg.counter = UInt32.ofBitVec m.counter → recvSeed st_prov msg = some seed :=
    fun msg hv hr hcn => hseed_pk msg hv hr (hcn.trans hctr₀.symm)
  obtain ⟨hrk_oi, hFresh⟩ := hNJ p st₀ st_prov m pk seed rIdx srcIdx skIdx hst_prov hseed_m hlog hγ_pk hJunk
  have hrs := hseed_pk { msg₀ with ratchetKey := pk } hver₀ rfl rfl
  obtain ⟨c₀, b, c₀', hrcf, hcons⟩ := snjf_recvChainFor_of_recvSeed hrs
  change recvChainFor st_prov.toDRState pk = some (c₀, b) at hrcf
  change consumeMessageKey c₀ msg₀.counter = some (seed, c₀') at hcons
  have hγ_msg₀ : gamma interpretation S g msg₀.ratchetKey = gamma interpretation S g pk :=
    (((ht₀.2.2.2 msg₀ hparse₀).2.2.2 m htry).2.1).trans hγ_pk.symm
  by_cases hrk_eq : msg₀.ratchetKey = pk
  · exact rcv_skippedVar_of_rk_eq interpretation hEq r S g ms body ptBytes m st_prov
      t₀ pk seed k_own msg₀ hSkel hABS' hreach htry ht₀ hparse₀ hver₀ hctr₀ hNotCol
      hst_prov hrk_eq (hseed_pk msg₀ hver₀ hrk_eq rfl) hk_own hMacBytes hDecOk
  cases b with
  | false =>
    obtain ⟨hc₀_mem, hc₀_rk⟩ := svk_recvChainFor_false' hrcf; subst hc₀_rk
    cases hVar : c₀.ratchetKey.view? DY.X25519.Variant.SubF with
    | none =>
      exact absurd (TR.G1.rk_eq_of_noncolliding_caseA' interpretation hEq r S g ms hHist hIW
        hst_prov hc₀_mem hCaseA' hVar hparse₀ hver₀ hγ_msg₀ hNotCol) hrk_eq
    | some _ =>
      have hrkK := rk_attackerKnows_of_rkKnownOrInit_variant hrk_oi hVar
      obtain ⟨t₁, msg₁, ht₁, hparse₁, hver₁, hrk₁, hctr₁, hseed₁, hk_own₁, hMacBytes₁, hNotCol₁⟩ :=
        hRes body m t₀ msg₀ st_prov c₀ c₀' seed k_own hHist hIW htry ht₀ hparse₀ hver₀ hNotCol
          hNotRS hst_prov hc₀_mem hγ_pk hrkK hcons hk_own hMacBytes
      exact rcv_skippedVar_of_rk_eq interpretation hEq r S g ms body ptBytes m st_prov
        t₁ c₀.ratchetKey seed k_own msg₁ hSkel hABS' hreach htry ht₁ hparse₁
        hver₁ (hctr₁.trans hctr₀) hNotCol₁ hst_prov hrk₁ hseed₁ hk_own₁ hMacBytes₁ hDecOk
  | true =>
    have hcons' : consumeMessageKey c₀ (UInt32.ofBitVec m.counter) = some (seed, c₀') := hctr₀ ▸ hcons
    obtain ⟨st₁_post, c₁, hst₁_post, hc₁, hcpk, hNotLow⟩ := hFresh c₀ hrcf
    cases hVar : pk.view? DY.X25519.Variant.SubF with
    | none =>
      have hγ₁ : gamma interpretation S g msg₀.ratchetKey = gamma interpretation S g c₁.ratchetKey := hcpk ▸ hγ_msg₀
      exact absurd ((TR.G1.rk_eq_of_noncolliding_caseA' interpretation hEq r S g ms hHist hIW
        hst₁_post hc₁ (hcpk.symm ▸ hCaseA') (hcpk.symm ▸ hVar) hparse₀ hver₀ hγ₁ hNotCol).trans hcpk) hrk_eq
    | some x =>
      have hrkK := rk_attackerKnows_of_rkKnownOrInit_variant hrk_oi hVar
      cases hfind : findRecvChain st_prov.recv msg₀.ratchetKey with
      | some c_ex =>
        by_cases hSeedK : seed.AttackerKnows (runTraceMoves r ms)
        · exact skippedVar_of_seedKnown' interpretation hEq r S g ms body ptBytes m st_prov
            t₀ pk seed k_own msg₀ htry ht₀ hparse₀ hver₀ hctr₀ hrkK hSeedK hγ_pk hMacBytes hPeerK hMyK
        · exact (hAliasLoc c₀ c_ex hrcf hfind hrk_eq hJunk ⟨x, hVar⟩ hrkK hSeedK).elim
      | none =>
        by_cases hbase : DY.X25519.normalizeX25519Key msg₀.ratchetKey = DY.X25519.normalizeX25519Key pk
        · cases hVar₀ : msg₀.ratchetKey.view? DY.X25519.Variant.SubF with
          | some y =>
            exact skippedVar_of_fresh_sameBase_variant_ex interpretation hEq r S g ms body ptBytes m
              st_prov c₀ c₀' t₀ pk seed k_own msg₀ y hSkel hABS' hreach htry ht₀ hparse₀
              hver₀ hctr₀ hNotCol hst_prov hrcf hcons' hk_own hrkK hγ_pk hMacBytes hPeerK hMyK hDecOk
              hbase hfind hVar₀
          | none =>
            exact Symbolic.Swarm.CREF.TR.RecvDecStep.SkippedVarFresh.skippedVar_of_fresh_dhPk
              interpretation hEq r hwf S g ms body ptBytes m
              st_prov st₁_post c₁ c₀ c₀' t₀ pk seed k_own msg₀ x hRun hreach htry ht₀ hparse₀
              hver₀ hctr₀ hNotCol hst_prov hst₁_post hc₁ hcpk hCaseA' hVar hJunk hrk_eq hrcf hcons'
              hk_own hHist hIW hrkK hγ_pk hMacBytes hPeerK hMyK hDecOk hbase hVar₀
        · exact (Symbolic.Swarm.CREF.TR.RecvDecStep.SkippedVarLit.false_of_skippedVar_diffBase
            interpretation hEq r S g ms body m
            st₁_post c₁ t₀ pk msg₀ ht₀ hparse₀ hver₀ htry hNotCol hst₁_post hc₁ hcpk hCaseA' hrk_eq
            hHist hIW hγ_pk hbase hNotLow).elim

/-- Discharges `SkippedPkDispatchAtKPure` from `CleanBy`, non-junk skipped-key provenance, and byte-chain reselection. -/
theorem skipped_pk_dispatch_atK'
    {interpretation : ExternInterpretation} (hext : ExternContractsHoldCli interpretation)
    {r : ProtocolSetup} (hwf : ProtocolSetupWF r) {S : OpaqueSymbolSemantics} {who : List Participant} {ok : Nat → Bool}
    {g : Ghost} {ms : List Move} {acc : List MachineEvent} (hc : CleanBy interpretation r S who ok g ms acc)
    (hNJ : RcvSkippedNotJunkSeedProvAt interpretation r S g ms)
    (hRes : RcvByteChainReselectAt interpretation r S g ms acc)
    (hbf : TR.SkippedInstallByteFresh interpretation S g r ms)
    (hAliasB : SkippedFreshAliasExclB interpretation r S g ms acc) :
    SkippedPkDispatchAtKPure interpretation r S g ms acc := by
  intro p stateIdx₀ body ptBytes m st₀ st_prov t₀ pk seed k_own msg₀ rIdx srcIdx skIdx
    htry ht₀ hparse₀ hver₀ hctr₀ hNotCol₀ hNotRS₀ hst₀ hst_prov hik_eq hseed_pk hk_own hk_def
    hlog hHist hIW _hSeedK_var hγ_pk hMacBytes hPeerK hMyK hDecOk
  have hRun : ModelRun r ms := hc.matched.2.1; have hreach : (runTraceMoves r ms).Reachable reachability := hRun.2.2.1.1
  have hγ_msg₀ : gamma interpretation S g msg₀.ratchetKey = gamma interpretation S g pk :=
    (((ht₀.2.2.2 msg₀ hparse₀).2.2.2 m htry).2.1).trans hγ_pk.symm
  have hst₀_at : TR.G1.TRStateStoredAt p st₀ stateIdx₀ (runTraceMoves r ms) :=
    TR.FreshSigma.at?_eq_some_of_getLocalState_some hst₀
  have hst₀_avail : st₀ ∈ availableStates r (runTraceMoves r ms) :=
    TR.G1.mem_availableStates_of_trStateStoredAt r ms hst₀_at
  have hik₀ : IkShapeTR r (runTraceMoves r ms) p st₀ := ikShapeTR_of_trStateStoredAt hRun hst₀_at
  obtain ⟨_hrkK, _hpost, hProvMB⟩ :=
    provEvTR_reachable hreach (st₀.sessionInfo p) pk (UInt32.ofBitVec m.counter) seed rIdx srcIdx skIdx hlog
  have hConcl : TR.RecvDecStep.SkippedVarKnownCk.SkippedVarConcl interpretation r S g ms body ptBytes m st_prov pk seed k_own := by
    rcases hProvMB with
      ⟨p₀, st₀_src, c₀, fresh, c₀', hst₀_src_at, hsinfo_src, hrc₀, hcons₀⟩ |
      ⟨p₀, st₀_src, c_src, hst₀_src_at, hsinfo_src, hinit_false, hc_src, hc_src_rk, hc_src_rIdx, hlt⟩
    · have hst₀_src_avail := TR.G1.mem_availableStates_of_trStateStoredAt r ms hst₀_src_at
      have hik_src := ikShapeTR_of_trStateStoredAt hRun hst₀_src_at
      obtain ⟨hIkEq, _, _⟩ := ik_eq_and_known_of_ikShapeTR r (runTraceMoves r ms) hwf hik_src hik₀ hsinfo_src
      have hpeer : st₀_src.peerIk = st_prov.peerIk := hIkEq.1.trans hik_eq.1.symm
      have hmy : st₀_src.myIk = st_prov.myIk := hIkEq.2.1.trans hik_eq.2.symm
      have hseed_src : ∀ msg, msg.version = messageVersion → msg.ratchetKey = pk →
          msg.counter = msg₀.counter → recvSeed st₀_src msg = some seed := by
        intro msg hver hrk_eq hctr_eq
        unfold recvSeed; simp only [hver, ↓reduceIte, hrk_eq, hrc₀, hctr_eq.trans hctr₀, hcons₀, Option.map]
      have hk_src : k_own ∈ ownKeys r (runTraceMoves r ms) st₀_src msg₀ := by
        subst hk_def; unfold ownKeys
        refine List.mem_map_of_mem (List.mem_filter.mpr ⟨hst₀_avail, ?_⟩); rw [hIkEq.2.2]; exact beq_self_eq_true _
      have hMac_src : body.drop (body.length - 8) = gamma interpretation S g
          (computeMac (trMsgKeys k_own seed).macKey st₀_src.peerIk st₀_src.myIk msg₀.wire) := by
        rw [hpeer, hmy]; exact hMacBytes
      have hsrc : TR.RecvDecStep.SkippedVarKnownCk.SkippedVarConcl interpretation r S g ms body ptBytes m st₀_src pk seed k_own :=
        snjf_skippedVarConcl' hext hwf hc hNJ hRes p body ptBytes m st₀ st₀_src t₀ pk seed
          k_own msg₀ rIdx srcIdx skIdx htry ht₀ hparse₀ hver₀ hctr₀ hNotCol₀ hNotRS₀ hst₀_src_avail
          hseed_src hk_src hlog hHist hIW hγ_pk hMac_src (hpeer ▸ hPeerK) (hmy ▸ hMyK) hDecOk
          (fun c₁ c_ex hrcf hfind _ _ _ _ _ =>
            TR.RecvDecStep.VarRecvSeedKnown.false_of_existing_of_byteFresh interpretation S g hfind
              hγ_msg₀ (hbf (st₀.sessionInfo p) pk (UInt32.ofBitVec m.counter) seed rIdx srcIdx skIdx p₀
                st₀_src c₁ hlog hst₀_src_at hrcf))
      exact snjf_skippedVarConcl_congr_ik hpeer hmy hsrc
    · exact snjf_skippedVarConcl' hext hwf hc hNJ hRes p body ptBytes m st₀ st_prov t₀ pk seed
        k_own msg₀ rIdx srcIdx skIdx htry ht₀ hparse₀ hver₀ hctr₀ hNotCol₀ hNotRS₀ hst_prov
        hseed_pk hk_own hlog hHist hIW hγ_pk hMacBytes hPeerK hMyK hDecOk
        (fun c₁ c_ex hrcf hfind hrk_ne hJunk hVar hrkK hSeedNK =>
          hAliasB p stateIdx₀ body m st₀ st_prov t₀ pk seed k_own msg₀ rIdx srcIdx skIdx c₁ c_ex
            htry ht₀ hparse₀ hver₀ hctr₀ hNotCol₀ hst₀ hst_prov hik_eq hseed_pk hk_def hlog hγ_pk
            hMacBytes hrcf hfind hrk_ne hJunk hVar hrkK hSeedNK
            ⟨p₀, st₀_src, c_src, hst₀_src_at, hsinfo_src, hinit_false, hc_src, hc_src_rk, hc_src_rIdx, hlt⟩)
  obtain ⟨t₁, msg₁, ht₁, hparse₁, hver₁, hrk₁, hctr₁, hMacBytes₁, hDisj₁⟩ := hConcl
  have hseed_kdf := exists_kdfCk_of_recvSeed (hseed_pk msg₁ hver₁ hrk₁ (hctr₁.trans hctr₀.symm))
  obtain ⟨t₂, msg₂, ht₂, hparse₂, hver₂, hrk₂, hctr₂, hMacBytes₂, hOut⟩ :=
    g1_disj_to_salt_form_at interpretation r S g ms body ptBytes m st_prov
      t₁ pk seed k_own msg₁ hreach hseed_kdf ht₁ hparse₁ hver₁ hrk₁ hMacBytes₁ hDecOk hDisj₁
  exact ⟨t₂, msg₂, ht₂, hparse₂, hver₂, hrk₂, hctr₂.trans (hctr₁.trans hctr₀.symm), hMacBytes₂, hOut⟩

end Symbolic.Swarm.CREF.CliPureRcv.RecvWirePure
