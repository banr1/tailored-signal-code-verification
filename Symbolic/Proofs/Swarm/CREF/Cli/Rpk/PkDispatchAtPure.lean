/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.TR.SkippedVarFresh
import DY.Bytes.Basic
import DY.ALaCarte.Basic
import DY.Actions.Random
import DY.EquationalTheory.DiffieHellman
import Symbolic.Specifications.Model.EquationalTheory.X25519
public import Symbolic.Proofs.Swarm.CREF.TR.G1.LitKeyKnown
public import Symbolic.Proofs.Swarm.CREF.TR.StoredRk
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.G1.CkSafeTR
import Symbolic.Proofs.Swarm.CREF.TR.G1.LitKeyKnownSInv
import Symbolic.Proofs.Swarm.CREF.TR.G1.SpqrRkForgedMac
import Symbolic.Proofs.Swarm.CREF.TR.HonestPqNoTrWire
import Symbolic.Proofs.Swarm.CREF.TR.RecvRep
import Symbolic.Proofs.Swarm.CREF.TR.PQGamma -- shake: keep
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Actions.Random

/-!
# Ratchet-Key Dispatch Helpers at a Provenance State

Defines `AuthenticDecryptRepB3AtSt` and `NoRatchetPkDispatchAtSt`, and upgrades
`G1.AuthenticDecryptRepB3_g1` witnesses and skipped-key attacker-knowledge cases to the
provenance-state salt form.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.CliPure.TR.RecvDecStepAt
open Symbolic.Swarm.CREF.TR hiding gamma_concat leValue_leBytes length_leBytes p25519_lt p25519_pos uOf_leBytes uOf_lt

cref_open

open DY DY.Comparse DY.Literal DY.Libsignal DY.DiffieHellman
open DY.Libsignal.TripleRatchet (RecvChain recvChainFor findRecvChain consumeMessageKey computeMac
  messageVersion x25519LowOrder createChain)
open DY.Libsignal.Refinement (ExternCryptoLawsHold aesCbcDecryptSymbol)
open DY.Libsignal.TripleRatchet
open CryptoGames.LibsignalSession (SignalMessage)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoProofLib.Refinement (ExternInterpretation)
open Symbolic.Swarm.CREF.TR.RecvRep hiding gamma_trWireMsg gamma_litOf
open Symbolic.Swarm.CREF.TR.RecvDecStep.SkippedVarKnownCk (SkippedVarConcl)

abbrev SpqrSem_pdapd27 := OpaqueSymbolSemantics

theorem svk_recvChainFor_false' {st : TRState} {pk : DY.Bytes} {c : RecvChain}
    (h : recvChainFor st.toDRState pk = some (c, false)) :
    c ∈ st.recv ∧ c.ratchetKey = pk := by
  unfold recvChainFor at h
  split at h
  · next c' hf =>
    injection h with h; injection h with hc _; subst c'
    unfold DY.Libsignal.TripleRatchet.findRecvChain at hf
    have hbeq := List.find?_some hf
    exact ⟨List.mem_of_find?_eq_some hf, eq_of_beq hbeq⟩
  · split at h <;> cases h

/-- Salt-form authentic decrypt representation at a fixed provenance state `st_prov`. -/
def AuthenticDecryptRepB3AtSt (interpretation : ExternInterpretation) (r₀ : ProtocolSetup) (S : SpqrSem_pdapd27)
    (g : Ghost) (ms₁ : List Move) (_body pt : HwBytes) (_t₀ : DY.Bytes) (msg₀ : TRSignalMsg)
    (st_prov : TRState) (_salt seed : DY.Bytes) : Prop :=
  ∃ (st_s : TRState) (t_c coinsLen : Nat),
    st_s ∈ availableStates r₀ (runTraceMoves r₀ ms₁) ∧
    msg₀.pqRatchet = (DY.Spqr.spqrSend st_s.spqr (randTerm t_c coinsLen)).2.2 ∧
    DY.Spqr.spqrEmptyMsg msg₀.pqRatchet = false ∧
    ∃ (pqSalt ptTerm : DY.Bytes),
      pqSalt.AttackerKnows (runTraceMoves r₀ ms₁) ∧
      msg₀.mac = computeMac (trMsgKeys pqSalt seed).macKey st_prov.peerIk st_prov.myIk msg₀.wire ∧
      DY.SymEnc.symDec (trMsgKeys pqSalt seed).cipherKey (trMsgKeys pqSalt seed).iv msg₀.ciphertext = some ptTerm ∧
      gamma interpretation S g ptTerm = pt

unseal DY.Bytes in
private instance subKdf0PKD (i : ExternInterpretation) (S : SpqrSem_pdapd27) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeKdf i) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, kdfFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩

private theorem gamma_kdfExtract_pkd (i : ExternInterpretation) (S : SpqrSem_pdapd27) (g : Ghost)
    (s ikm : DY.Bytes) :
    gamma i S g (KdfExtract.kdfExtract s ikm) =
      CryptoGames.HMAC.hmacWith (DY.Libsignal.Refinement.sha256CompressFunction i)
        (gamma i S g s) (gamma i S g ikm) := by
  unfold gamma gamma'
  show ((({ salt := s, ikm := ikm } : DY.KdfExtract.KdfExtract.SubF DY.Bytes).pack).rec (concretizeAll i S g)).bytes = _
  rw [DY.Bytes.rec_eq (concretizeKdf i) (concretizeAll i S g)]; rfl

private theorem gamma_trunc8_pkd (interpretation : ExternInterpretation) (S : SpqrSem_pdapd27) (g : Ghost)
    (x : DY.Bytes) :
    gamma interpretation S g (Trunc.trunc8 x) = (gamma interpretation S g x).take 8 := by
  unfold Trunc.trunc8 gamma gamma'
  show ((({input := x} : DY.Trunc.Trunc8.SubF DY.Bytes).pack).rec (concretizeAll interpretation S g)).bytes = _
  rw [DY.Bytes.rec_eq concretizeTrunc (concretizeAll interpretation S g)]; rfl

private theorem gamma_computeMac_congr_mk_tr
    (interpretation : ExternInterpretation) (S : SpqrSem_pdapd27) (g : Ghost)
    (mk₁ mk₂ peerIk myIk wire : DY.Bytes)
    (hmk : gamma interpretation S g mk₁ = gamma interpretation S g mk₂) :
    gamma interpretation S g (computeMac mk₁ peerIk myIk wire) =
      gamma interpretation S g (computeMac mk₂ peerIk myIk wire) := by
  unfold DY.Libsignal.TripleRatchet.computeMac DY.Libsignal.TripleRatchet.hmac
  rw [gamma_trunc8_pkd, gamma_trunc8_pkd, gamma_kdfExtract_pkd, gamma_kdfExtract_pkd, hmk]

private theorem gamma_computeMac_congr_wire_tr
    (interpretation : ExternInterpretation) (S : SpqrSem_pdapd27) (g : Ghost)
    (mk peerIk myIk w₁ w₂ : DY.Bytes)
    (hw : gamma interpretation S g w₁ = gamma interpretation S g w₂) :
    gamma interpretation S g (computeMac mk peerIk myIk w₁) =
      gamma interpretation S g (computeMac mk peerIk myIk w₂) := by
  unfold DY.Libsignal.TripleRatchet.computeMac DY.Libsignal.TripleRatchet.hmac
  rw [gamma_trunc8_pkd, gamma_trunc8_pkd, gamma_kdfExtract_pkd, gamma_kdfExtract_pkd,
      RecvRep.gamma_concat, RecvRep.gamma_concat, RecvRep.gamma_concat, RecvRep.gamma_concat, hw]

/-- Upgrade a `G1.AuthenticDecryptRepB3_g1` witness at `(t₁, msg₁, st_prov, seed, k_own)` (where
`seed = (kdfCk ck).2`) into either `seed.AttackerKnows` or a representation `(t₂, msg₂)` with
`AuthenticDecryptRepB3AtSt` and the salt-form equations. -/
theorem g1_disj_to_salt_form_at
    (interpretation : ExternInterpretation) (r₀ : ProtocolSetup) (S : SpqrSem_pdapd27) (g : Ghost) (ms₁ : List Move)
    (body ptBytes : HwBytes) (m : SignalMessage)
    (st_prov : TRState) (t₁ pk seed k_own : DY.Bytes) (msg₁ : TRSignalMsg)
    (hreach : (runTraceMoves r₀ ms₁).Reachable reachability)
    (hseed_kdf : ∃ ck, seed = (DY.Libsignal.TripleRatchet.kdfCk ck).2)
    (ht₁ : t₁ ∈ recvRepresentations interpretation r₀ S g ms₁ body)
    (hparse₁ : parseTrSignalMsg t₁ = some msg₁)
    (hver₁ : msg₁.version = messageVersion) (hrk₁ : msg₁.ratchetKey = pk)
    (hMacBytes₁ : body.drop (body.length - 8) =
      gamma interpretation S g (computeMac (trMsgKeys k_own seed).macKey st_prov.peerIk st_prov.myIk msg₁.wire))
    (hDecOk : interpretation aesCbcDecryptSymbol
      [m.ciphertext, gamma interpretation S g (trMsgKeys k_own seed).cipherKey,
       (gamma interpretation S g (trMsgKeys k_own seed).iv).take 16] = some ptBytes)
    (hDisj : seed.AttackerKnows (runTraceMoves r₀ ms₁) ∨
      G1.AuthenticDecryptRepB3_g1 interpretation r₀ S g ms₁ body ptBytes msg₁ st_prov seed k_own) :
    ∃ (t₂ : DY.Bytes) (msg₂ : TRSignalMsg),
      t₂ ∈ recvRepresentations interpretation r₀ S g ms₁ body ∧ parseTrSignalMsg t₂ = some msg₂ ∧
      msg₂.version = messageVersion ∧ msg₂.ratchetKey = pk ∧ msg₂.counter = msg₁.counter ∧
      body.drop (body.length - 8) =
        gamma interpretation S g (computeMac (trMsgKeys k_own seed).macKey st_prov.peerIk st_prov.myIk msg₂.wire) ∧
      (seed.AttackerKnows (runTraceMoves r₀ ms₁) ∨ ∃ salt ∈ honestSalts r₀ ms₁,
        AuthenticDecryptRepB3AtSt interpretation r₀ S g ms₁ body ptBytes t₂ msg₂ st_prov salt seed ∧
        gamma interpretation S g (computeMac (trMsgKeys k_own seed).macKey st_prov.peerIk st_prov.myIk msg₂.wire) =
          gamma interpretation S g (computeMac (trMsgKeys salt seed).macKey st_prov.peerIk st_prov.myIk msg₂.wire) ∧
        interpretation aesCbcDecryptSymbol
          [m.ciphertext, gamma interpretation S g (trMsgKeys salt seed).cipherKey,
           (gamma interpretation S g (trMsgKeys salt seed).iv).take 16] = some ptBytes) := by
  rcases hDisj with hSeedK | ⟨salt, hsalt_mem, ⟨hck_eq, hmk_eq, hiv_eq⟩, hAuth⟩
  · exact ⟨t₁, msg₁, ht₁, hparse₁, hver₁, hrk₁, rfl, hMacBytes₁, Or.inl hSeedK⟩
  · obtain ⟨t', msg', ptTerm, pqSalt, ht'_mem, ht'_kn, hpqSalt_kn, _hpq_gam, _ht'_gam,
      hparse', hver', hrk', hctr', _hpqMsg_gam, hmac', hdec', hpt_gam⟩ := hAuth
    have hwire₁_take := (ht₁.2.2.2 msg₁ hparse₁).1
    have hwire'_take := (ht'_mem.2.2.2 msg' hparse').1
    have hMacBytes' : body.drop (body.length - 8) =
        gamma interpretation S g (computeMac (trMsgKeys k_own seed).macKey st_prov.peerIk st_prov.myIk msg'.wire) := by
      rw [gamma_computeMac_congr_wire_tr interpretation S g _ _ _ msg'.wire msg₁.wire
        (hwire'_take.trans hwire₁_take.symm)]; exact hMacBytes₁
    rcases honest_encrypt_mac_pqRatchet_prov_or_keysKnown_tr hreach ht'_kn hparse' hmac' with
      ⟨st_s, t_c, coinsLen, hst_s, hpq_eq, hempty⟩ | ⟨_hck_kn, hmk_kn, _hiv_kn⟩
    · refine ⟨t', msg', ht'_mem, hparse', hver'.trans hver₁, hrk'.trans hrk₁, hctr', hMacBytes',
        Or.inr ⟨salt, hsalt_mem,
          ⟨st_s, t_c, coinsLen, hst_s, hpq_eq, hempty, pqSalt, ptTerm, hpqSalt_kn, hmac', hdec', hpt_gam⟩,
          gamma_computeMac_congr_mk_tr interpretation S g _ _ _ _ _ hmk_eq.symm, ?_⟩⟩
      rw [hck_eq, hiv_eq]; exact hDecOk
    · obtain ⟨ck, hseed_eq⟩ := hseed_kdf
      have hSeedK : seed.AttackerKnows (runTraceMoves r₀ ms₁) := by
        rw [hseed_eq] at hmk_kn ⊢; exact G1.seed_known_of_macKey_known_tr hreach hmk_kn
      exact ⟨t₁, msg₁, ht₁, hparse₁, hver₁, hrk₁, rfl, hMacBytes₁, Or.inl hSeedK⟩

theorem exists_kdfCk_of_consumeMessageKey
    {c c' : RecvChain} {counter : UInt32} {seed : DY.Bytes}
    (hcons : consumeMessageKey c counter = some (seed, c')) :
    ∃ ck, seed = (DY.Libsignal.TripleRatchet.kdfCk ck).2 := by
  unfold consumeMessageKey at hcons
  split at hcons; · cases hcons
  split at hcons; · cases hcons
  split at hcons; · cases hcons
  simp only [Option.some.injEq, Prod.mk.injEq] at hcons
  exact ⟨_, hcons.1.symm⟩

theorem exists_kdfCk_of_recvSeed
    {st : TRState} {msg : TRSignalMsg} {seed : DY.Bytes}
    (hseed : recvSeed st msg = some seed) :
    ∃ ck, seed = (DY.Libsignal.TripleRatchet.kdfCk ck).2 := by
  unfold recvSeed at hseed
  split at hseed
  · rcases hrcf : recvChainFor st.toDRState msg.ratchetKey with _ | ⟨c, fresh⟩
    · rw [hrcf] at hseed; cases hseed
    · rw [hrcf] at hseed; dsimp only [Option.map] at hseed
      rcases hcons : consumeMessageKey c msg.counter with _ | ⟨s', c'⟩
      · rw [hcons] at hseed; cases hseed
      · rw [hcons] at hseed; injection hseed with hs; subst hs
        exact exists_kdfCk_of_consumeMessageKey hcons
  · cases hseed

private theorem x25519LowOrder_eq_of_x25519Key_eq_pkd {pk₁ pk₂ : DY.Bytes}
    (h : DY.X25519.normalizeX25519Key pk₁ = DY.X25519.normalizeX25519Key pk₂) :
    x25519LowOrder pk₁ = x25519LowOrder pk₂ := by unfold x25519LowOrder; rw [h]

private theorem createChain_eq_of_x25519Key_eq_pkd (rk : DY.Bytes) {pk₁ pk₂ : DY.Bytes} (dhs : DY.Bytes)
    (h : DY.X25519.normalizeX25519Key pk₁ = DY.X25519.normalizeX25519Key pk₂) :
    createChain rk pk₁ dhs = createChain rk pk₂ dhs := by unfold createChain DY.X25519.agree; rw [h]

private theorem consumeMessageKey_snd_eq_of_chainKey_index_eq_pkd
    {c₁ c₂ c₁' : RecvChain} {counter : UInt32} {seed : DY.Bytes}
    (hck : c₁.chainKey = c₂.chainKey) (hidx : c₁.index = c₂.index)
    (hcons : consumeMessageKey c₁ counter = some (seed, c₁')) :
    ∃ c₂', consumeMessageKey c₂ counter = some (seed, c₂') ∧
      seed = (DY.Libsignal.TripleRatchet.kdfCk (DY.Libsignal.TripleRatchet.chainKeyAt c₁.chainKey (counter.toNat - c₁.index.toNat))).2 := by
  unfold consumeMessageKey at hcons ⊢; rw [← hck, ← hidx]
  split at hcons; · cases hcons
  next h1 =>
  split at hcons; · cases hcons
  next h2 =>
  split at hcons; · cases hcons
  next h3 =>
  simp only [Option.some.injEq, Prod.mk.injEq] at hcons
  rcases hcons with ⟨hseed, rfl⟩; simp only [h1, h2, h3, ↓reduceIte]
  exact ⟨_, congrArg (fun s => some (s, _)) hseed, hseed.symm⟩

private theorem recvChainFor_true_inv_pkd {st : DY.Libsignal.TripleRatchet.DRState} {pk : DY.Bytes} {c₀ : RecvChain}
    (hrcf : recvChainFor st pk = some (c₀, true)) :
    findRecvChain st.recv pk = none ∧ x25519LowOrder pk = false ∧
    c₀ = { ratchetKey := pk, chainKey := (createChain st.rk pk st.dhs).2,
           index := 0, rIdx := st.rIdx + 2 } := by
  unfold recvChainFor at hrcf
  split at hrcf; · cases hrcf
  next hfind =>
  split at hrcf; · cases hrcf
  next hlow =>
  simp only [Option.some.injEq, Prod.mk.injEq] at hrcf
  exact ⟨hfind, Bool.eq_false_iff.mpr hlow, hrcf.1.symm⟩

theorem recvSeed_eq_some_of_fresh_sameBase'
    {st₀_src : TRState} {pk seed : DY.Bytes} {c₀ c₀' : RecvChain} {msg₀ : TRSignalMsg}
    {counter : UInt32} (hver₀ : msg₀.version = messageVersion) (hctr₀ : msg₀.counter = counter)
    (hrcf : recvChainFor st₀_src.toDRState pk = some (c₀, true))
    (hcons : consumeMessageKey c₀ counter = some (seed, c₀'))
    (hbase : DY.X25519.normalizeX25519Key msg₀.ratchetKey = DY.X25519.normalizeX25519Key pk)
    (hfind : findRecvChain st₀_src.recv msg₀.ratchetKey = none) :
    recvSeed st₀_src msg₀ = some seed ∧
    ∃ ck, seed = (DY.Libsignal.TripleRatchet.kdfCk ck).2 := by
  obtain ⟨_, hlow_pk, hc₀_eq⟩ := recvChainFor_true_inv_pkd hrcf
  have hlow_msg : x25519LowOrder msg₀.ratchetKey = false :=
    (x25519LowOrder_eq_of_x25519Key_eq_pkd hbase).trans hlow_pk
  have hcc := createChain_eq_of_x25519Key_eq_pkd st₀_src.rk st₀_src.dhs hbase
  let c_msg : RecvChain :=
    { ratchetKey := msg₀.ratchetKey,
      chainKey := (createChain st₀_src.rk msg₀.ratchetKey st₀_src.dhs).2,
      index := 0, rIdx := st₀_src.rIdx + 2 }
  have hck_eq : c₀.chainKey = c_msg.chainKey := by rw [hc₀_eq]; dsimp only [c_msg]; rw [hcc]
  have hidx_eq : c₀.index = c_msg.index := by rw [hc₀_eq]
  obtain ⟨c_msg', hcons_msg, hseed_kdf⟩ :=
    consumeMessageKey_snd_eq_of_chainKey_index_eq_pkd hck_eq hidx_eq (hctr₀ ▸ hcons)
  have hrcf_msg : recvChainFor st₀_src.toDRState msg₀.ratchetKey = some (c_msg, true) := by
    unfold recvChainFor
    have hfind' : findRecvChain st₀_src.toDRState.recv msg₀.ratchetKey = none := hfind
    simp [hfind', hlow_msg, c_msg]
  unfold recvSeed; simp [hver₀, hrcf_msg, hcons_msg]; exact ⟨_, hseed_kdf⟩

theorem skippedVar_of_seedKnown'
    (interpretation : ExternInterpretation) (hEq : ExternCryptoLawsHold interpretation)
    (r₀ : ProtocolSetup) (S : SpqrSem_pdapd27) (g' : Ghost) (ms₁ : List Move)
    (body ptext : HwBytes) (m : SignalMessage) (st₀_src : TRState)
    (t₀ pk seed k_own : DY.Bytes) (msg₀ : TRSignalMsg)
    (htry : SignalMessage.tryFrom protoSignalCodec body = .ok m)
    (ht₀ : t₀ ∈ recvRepresentations interpretation r₀ S g' ms₁ body)
    (hparse₀ : parseTrSignalMsg t₀ = some msg₀)
    (hver₀ : msg₀.version = messageVersion) (hctr₀ : msg₀.counter = UInt32.ofBitVec m.counter)
    (hrkK : pk.AttackerKnows (runTraceMoves r₀ ms₁)) (hSeedK : seed.AttackerKnows (runTraceMoves r₀ ms₁))
    (hγ_pk : gamma interpretation S g' pk = m.senderRatchetKey.bytes.toList)
    (hMacBytes : body.drop (body.length - 8) =
      gamma interpretation S g' (computeMac (trMsgKeys k_own seed).macKey st₀_src.peerIk st₀_src.myIk msg₀.wire))
    (hPeerK : st₀_src.peerIk.AttackerKnows (runTraceMoves r₀ ms₁))
    (hMyK : st₀_src.myIk.AttackerKnows (runTraceMoves r₀ ms₁)) :
    SkippedVarConcl interpretation r₀ S g' ms₁ body ptext m st₀_src pk seed k_own := by
  obtain ⟨t₁, msg₁, ht₁_rep, hparse₁, hver₁, hrk₁, hctr₁, hMacBytes₁⟩ :=
    Symbolic.Swarm.CREF.TR.RecvDecStep.SkippedVarKnownCk.svk_rk_switch_of_seedKnown
      interpretation hEq r₀ S g' ms₁ body m htry
      ht₀ hparse₀ hrkK hSeedK hMacBytes hPeerK hMyK hγ_pk
  exact ⟨t₁, msg₁, ht₁_rep, hparse₁, hver₁.trans hver₀, hrk₁, hctr₁.trans hctr₀,
    hMacBytes₁, Or.inl hSeedK⟩

theorem skippedVar_of_litJunk'
    (interpretation : ExternInterpretation) (hEq : ExternCryptoLawsHold interpretation)
    (r₀ : ProtocolSetup) (S : SpqrSem_pdapd27) (g' : Ghost) (ms₁ : List Move)
    (body ptext : HwBytes) (m : SignalMessage) (st₀_src : TRState)
    (t₀ pk seed k_own : DY.Bytes) (msg₀ : TRSignalMsg)
    {ses : DY.Libsignal.TripleRatchet.SessionInfo} {rIdx srcIdx skIdx : Nat}
    (hreach : (runTraceMoves r₀ ms₁).Reachable reachability)
    (htry : SignalMessage.tryFrom protoSignalCodec body = .ok m)
    (ht₀ : t₀ ∈ recvRepresentations interpretation r₀ S g' ms₁ body)
    (hparse₀ : parseTrSignalMsg t₀ = some msg₀)
    (hver₀ : msg₀.version = messageVersion) (hctr₀ : msg₀.counter = UInt32.ofBitVec m.counter)
    (hlog : (runTraceMoves r₀ ms₁).EventLoggedAt
      (TREvent.SkippedKeyStored ses pk (UInt32.ofBitVec m.counter) seed rIdx srcIdx) skIdx)
    (hj : G1.LitJunk pk)
    (hγ_pk : gamma interpretation S g' pk = m.senderRatchetKey.bytes.toList)
    (hMacBytes : body.drop (body.length - 8) =
      gamma interpretation S g' (computeMac (trMsgKeys k_own seed).macKey st₀_src.peerIk st₀_src.myIk msg₀.wire))
    (hPeerK : st₀_src.peerIk.AttackerKnows (runTraceMoves r₀ ms₁))
    (hMyK : st₀_src.myIk.AttackerKnows (runTraceMoves r₀ ms₁)) :
    SkippedVarConcl interpretation r₀ S g' ms₁ body ptext m st₀_src pk seed k_own := by
  obtain ⟨hrkK, hSeedK⟩ :=
    G1.skippedSeedKnownTR_of_sinv (G1.sinvTR_reachable G1.ckKnownCasesTR hreach) hlog hj
  exact skippedVar_of_seedKnown' interpretation hEq r₀ S g' ms₁ body ptext m st₀_src
    t₀ pk seed k_own msg₀ htry ht₀ hparse₀ hver₀ hctr₀ hrkK hSeedK hγ_pk hMacBytes hPeerK hMyK

theorem rk_attackerKnows_of_rkKnownOrInit_variant {tr : ExecTrace} {pk : DY.Bytes}
    {x : DY.X25519.Variant.SubF DY.Bytes}
    (hrk_oi : RkKnownOrInit tr pk) (hVar : pk.view? DY.X25519.Variant.SubF = some x) :
    pk.AttackerKnows tr := by
  rcases hrk_oi with hak | heq; · exact hak
  rw [heq] at hVar
  rw [show (DY.DiffieHellman.dhPk (randTerm 2 32)).view? DY.X25519.Variant.SubF = none from
    Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _] at hVar
  cases hVar

theorem rk_attackerKnows_of_rkKnownOrInit_litJunk {tr : ExecTrace} {pk : DY.Bytes}
    (hrk_oi : RkKnownOrInit tr pk) (hj : G1.LitJunk pk) :
    pk.AttackerKnows tr := by
  rcases hrk_oi with hak | heq; · exact hak
  refine absurd ?_ (hj 2)
  rw [heq]
  unfold DY.X25519.normalizeX25519Key
  dsimp only [DY.DiffieHellman.dhPk, DY.DiffieHellman.CanDH.dhPk]
  rw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.X25519.Variant.SubF]

unseal DY.Bytes in
private instance subDhPkPKD (i : ExternInterpretation) (S : SpqrSem_pdapd27) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeDhPk i) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, dhFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subVariant0PKD (i : ExternInterpretation) (S : SpqrSem_pdapd27) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeVariant i) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, x25519Funs, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩

private theorem not_mem_ptAtoms_of_view_random_none_pkd
    (r₀ : ProtocolSetup) (ms : List Move) (u : DY.Bytes) (h : u.view? DY.Random.Random = none) :
    u ∉ plaintextTerms (runVis r₀ ms) ++ [] := by
  intro hp; rw [List.append_nil] at hp
  exact G1.not_mem_ptAtoms_of_view_random_isNone r₀ ms [] (fun _ hv => nomatch hv) u
    (Option.isNone_iff_eq_none.mpr h) (by rwa [List.append_nil])

unseal DY.Bytes in
private theorem notSpqrHeaded_dhPk_pkd (a : DY.Bytes) : G1.notSpqrHeaded (DY.DiffieHellman.dhPk a) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    exact Option.isNone_iff_eq_none.mpr (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)

unseal DY.Bytes in
private theorem notOpaqueHeaded_dhPk_pkd (a : DY.Bytes) : G1.notOpaqueHeaded (DY.DiffieHellman.dhPk a) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    exact Option.isNone_iff_eq_none.mpr (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)

unseal DY.Bytes in
private theorem dhPk_not_mem_ptAtoms_pkd (r₀ : ProtocolSetup) (ms : List Move) (a : DY.Bytes) :
    DY.DiffieHellman.dhPk a ∉ plaintextTerms (runVis r₀ ms) ++ [] :=
  not_mem_ptAtoms_of_view_random_none_pkd r₀ ms _
    (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)

unseal DY.Bytes in
private theorem variant_pack_not_mem_ptAtoms_pkd (r₀ : ProtocolSetup) (ms : List Move)
    (x : DY.X25519.Variant.SubF DY.Bytes) : x.pack ∉ plaintextTerms (runVis r₀ ms) ++ [] :=
  not_mem_ptAtoms_of_view_random_none_pkd r₀ ms _
    (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)

/-- No-ratchet ratchet-key dispatch hypothesis formulated with `AuthenticDecryptRepB3AtSt`. -/
def NoRatchetPkDispatchAtSt (interpretation : ExternInterpretation) (r₀ : ProtocolSetup) (S : SpqrSem_pdapd27)
    (g : Ghost) (ms₁ : List Move) (_τ₁ : List MachineEvent) : Prop :=
  ∀ (p : Participant) (stateIdx₀ : Nat) (body ptBytes : HwBytes) (m : SignalMessage) (st₀ : TRState)
    (c c' : RecvChain) (t₀ seed k_own : DY.Bytes) (msg₀ : TRSignalMsg),
    ModelRun r₀ ms₁ → (runTraceMoves r₀ ms₁).Reachable reachability →
    SignalMessage.tryFrom protoSignalCodec body = .ok m →
    t₀ ∈ recvRepresentations interpretation r₀ S g ms₁ body → parseTrSignalMsg t₀ = some msg₀ →
    msg₀.version = messageVersion → msg₀.counter = UInt32.ofBitVec m.counter →
    ¬RecvCollision interpretation r₀ S g ms₁ t₀ →
    ¬ReselectCollision interpretation r₀ S g ms₁ t₀ →
    ((PersistentLocalState.getLocalState p stateIdx₀ : Traceful TRState).run (runTraceMoves r₀ ms₁)).1 = some st₀ →
    c ∈ st₀.recv → consumeMessageKey c msg₀.counter = some (seed, c') →
    (msg₀.ratchetKey = c.ratchetKey → recvSeed st₀ msg₀ = some seed) →
    k_own ∈ ownKeys r₀ (runTraceMoves r₀ ms₁) st₀ msg₀ →
    Symbolic.Swarm.CREF.TR.G1.RecvHistInvTR interpretation S g r₀ ms₁ →
    Symbolic.Swarm.CREF.TR.G1.InstallWitnessTR r₀ (runTraceMoves r₀ ms₁) →
    RkKnownOrInit (runTraceMoves r₀ ms₁) c.ratchetKey →
    gamma interpretation S g c.ratchetKey = m.senderRatchetKey.bytes.toList →
    body.drop (body.length - 8) =
      gamma interpretation S g (computeMac (trMsgKeys k_own seed).macKey st₀.peerIk st₀.myIk msg₀.wire) →
    st₀.peerIk.AttackerKnows (runTraceMoves r₀ ms₁) → st₀.myIk.AttackerKnows (runTraceMoves r₀ ms₁) →
    interpretation DY.Libsignal.Refinement.aesCbcDecryptSymbol
      [m.ciphertext, gamma interpretation S g (trMsgKeys k_own seed).cipherKey,
       (gamma interpretation S g (trMsgKeys k_own seed).iv).take 16] = some ptBytes →
    ∃ (t₁ : DY.Bytes) (msg₁ : TRSignalMsg),
      t₁ ∈ recvRepresentations interpretation r₀ S g ms₁ body ∧ parseTrSignalMsg t₁ = some msg₁ ∧
      msg₁.version = messageVersion ∧ msg₁.ratchetKey = c.ratchetKey ∧ msg₁.counter = msg₀.counter ∧
      body.drop (body.length - 8) =
        gamma interpretation S g (computeMac (trMsgKeys k_own seed).macKey st₀.peerIk st₀.myIk msg₁.wire) ∧
      (seed.AttackerKnows (runTraceMoves r₀ ms₁) ∨ ∃ salt ∈ honestSalts r₀ ms₁,
        AuthenticDecryptRepB3AtSt interpretation r₀ S g ms₁ body ptBytes t₁ msg₁ st₀ salt seed ∧
        gamma interpretation S g (computeMac (trMsgKeys k_own seed).macKey st₀.peerIk st₀.myIk msg₁.wire) =
          gamma interpretation S g (computeMac (trMsgKeys salt seed).macKey st₀.peerIk st₀.myIk msg₁.wire) ∧
        interpretation DY.Libsignal.Refinement.aesCbcDecryptSymbol
          [m.ciphertext, gamma interpretation S g (trMsgKeys salt seed).cipherKey,
           (gamma interpretation S g (trMsgKeys salt seed).iv).take 16] = some ptBytes)

end Symbolic.Swarm.CREF.CliPure.TR.RecvDecStepAt
