/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.TR.G1.LitKeyKnown
import DY.ALaCarte.Basic
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.TrWireMsg
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.OpkSent
import Symbolic.Proofs.Swarm.COMPOSED.CompDhsOrigin
import Symbolic.Proofs.Swarm.COMPOSED.CompTermAlgebra
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random

/-!
# Preservation of `SInvTR` Across `messageDecrypt`

Proves `sinvTR_messageDecrypt`: on a reachable composed trace satisfying `CkKnownCasesTRP` and
`DepthTR`, executing `TripleRatchet.messageDecrypt` preserves `SInvTR`.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.TR.G1

cref_open
open DY DY.Comparse DY.DiffieHellman DY.Literal DY.X25519
open DY.Libsignal.TripleRatchet
open DY.Libsignal.TripleRatchet (DRState RecvChain SessionInfo hmac createChain kdfCk chainKeyAt
  computeMac consumeMessageKey findRecvChain setRecvChain recvChainFor x25519LowOrder
  maxReceiverChains)
open Symbolic.Swarm.CREF.TR
open Symbolic.Swarm.COMPOSED.CompTrace
open Symbolic.Swarm.COMPOSED.CompRatchet
open Symbolic.Swarm.COMPOSED.CompTermAlgebra

attribute [local instance 2000]
  DY.Libsignal.Composed.instHasExecBytes
  DY.Libsignal.Composed.instHasExecTrace

/-! ## Algebra and `ChainOKTR` helpers -/

section RdecInjectivity
unseal DY.Bytes

private theorem rdec_kdfExtract_inj {s₁ i₁ s₂ i₂ : DY.Bytes}
    (h : KdfExtract.kdfExtract s₁ i₁ = KdfExtract.kdfExtract s₂ i₂) : s₁ = s₂ ∧ i₁ = i₂ := by
  have h1 := DY.BytesView.view_pack (SubF := DY.KdfExtract.KdfExtract.SubF) { salt := s₁, ikm := i₁ }
  have h2 := DY.BytesView.view_pack (SubF := DY.KdfExtract.KdfExtract.SubF) { salt := s₂, ikm := i₂ }
  change DY.Bytes.view? (KdfExtract.kdfExtract s₁ i₁) _ = _ at h1
  change DY.Bytes.view? (KdfExtract.kdfExtract s₂ i₂) _ = _ at h2
  rw [h, h2] at h1; injection h1 with h1; cases h1; exact ⟨rfl, rfl⟩

end RdecInjectivity

private theorem rdec_kdfCk_snd_inj {ck₁ ck₂ : DY.Bytes}
    (h : (kdfCk ck₁).2 = (kdfCk ck₂).2) : ck₁ = ck₂ :=
  (rdec_kdfExtract_inj h).1

private theorem rdec_litJunk_of_x25519Key_eq {pk pk' : DY.Bytes} (hj : LitJunk pk)
    (h : DY.X25519.normalizeX25519Key pk' = DY.X25519.normalizeX25519Key pk) : LitJunk pk' := by
  intro i ha; exact hj i (h ▸ ha)

private theorem rdec_randTerm_ne_createChain_snd (i n : Nat) (rk pk sk : DY.Bytes) :
    randTerm i n ≠ (createChain rk pk sk).2 := by
  intro h
  have h1 : saltDepth (randTerm i n) = 0 := saltDepth_mkRand i n
  have h2 : saltDepth (createChain rk pk sk).2 = saltDepth rk + 2 :=
    saltDepth_createChain_snd rk pk sk
  rw [h, h2] at h1; omega

private theorem rdec_randTerm_ne_pqxdhKdf_ck (i n : Nat) (ikm : DY.Bytes) :
    randTerm i n ≠ (DY.Libsignal.PQXDH.pqxdhKdf ikm).ck := by
  intro h
  have h1 : saltDepth (randTerm i n) = 0 := saltDepth_mkRand i n
  have h2 : saltDepth (DY.Libsignal.PQXDH.pqxdhKdf ikm).ck = 2 := saltDepth_pqxdhKdf_ck ikm
  rw [h, h2] at h1; omega

theorem rdec_chainOK_chainKeyAt {tr : ExecTrace} {pk ck : DY.Bytes}
    (h : ChainOKTR tr pk ck) (m : Nat) :
    ChainOKTR tr pk (chainKeyAt ck m) := by
  obtain ⟨b, k, rfl, hg, hb⟩ := h
  exact ⟨b, k + m, (chainKeyAt_add b k m).symm, hg, hb⟩

theorem rdec_chainOK_kdfCk_fst {tr : ExecTrace} {pk ck : DY.Bytes}
    (h : ChainOKTR tr pk ck) :
    ChainOKTR tr pk (kdfCk ck).1 := by
  obtain ⟨b, k, rfl, hg, hb⟩ := h
  exact ⟨b, k + 1, (chainKeyAt_succ_eq_kdfCk_fst b k).symm, hg, hb⟩

private theorem rdec_sinv_append_other {E : Type} [ExecTraceTypes.Has E] {tr : ExecTrace} {e : E}
    (hnone_tr : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option TREntry) = none)
    (hnone_st : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option TRStEntry) = none)
    (h : SInvTR tr) : SInvTR (tr.append e) where
  recv p st i hst c hc :=
    (h.recv p st i (trStateStoredAt_append_other hnone_st hst) c hc).imp
      (fun h => h.mono (Trace.append_le tr e)) id
  skip s pk n seed rIdx src j hev := by
    obtain ⟨ck, h1, h2⟩ := h.skip s pk n seed rIdx src j (eventLoggedAt_append_other hnone_tr hev)
    exact ⟨ck, h1, h2.mono (Trace.append_le tr e)⟩
  cks p st i hst := h.cks p st i (trStateStoredAt_append_other hnone_st hst)

private theorem rdec_sinv_append_tr {tr : ExecTrace} {ev : TREvent}
    (hev : ∀ s pk n seed rIdx src, ev ≠ TREvent.SkippedKeyStored s pk n seed rIdx src)
    (h : SInvTR tr) : SInvTR (tr.append (TREvE ev)) where
  recv p st i hst c hc :=
    (h.recv p st i (trStateStoredAt_append_other rfl hst) c hc).imp
      (fun h => h.mono (Trace.append_le tr _)) id
  skip s pk n seed rIdx src j hl := by
    rcases eventLoggedAt_append_same hl with ⟨_, hl⟩ | ⟨_, heq⟩
    · obtain ⟨ck, h1, h2⟩ := h.skip s pk n seed rIdx src j hl
      exact ⟨ck, h1, h2.mono (Trace.append_le tr _)⟩
    · exact absurd heq (hev s pk n seed rIdx src)
  cks p st i hst := h.cks p st i (trStateStoredAt_append_other rfl hst)

private theorem rdec_sinv_append_skip {tr : ExecTrace} {s : SessionInfo} {pk seed : DY.Bytes} {n : UInt32}
    {rIdx src : Nat} (hck : ∃ ck, seed = (kdfCk ck).2 ∧ ChainOKTR tr pk ck) (h : SInvTR tr) :
    SInvTR (tr.append (TREvE (TREvent.SkippedKeyStored s pk n seed rIdx src))) where
  recv p st i hst c hc :=
    (h.recv p st i (trStateStoredAt_append_other rfl hst) c hc).imp
      (fun h => h.mono (Trace.append_le tr _)) id
  skip s' pk' n' seed' rIdx' src' j hl := by
    rcases eventLoggedAt_append_same hl with ⟨_, hl⟩ | ⟨_, heq⟩
    · obtain ⟨ck, h1, h2⟩ := h.skip s' pk' n' seed' rIdx' src' j hl
      exact ⟨ck, h1, h2.mono (Trace.append_le tr _)⟩
    · injection heq with _ hpk _ hseed
      subst hpk hseed
      obtain ⟨ck, h1, h2⟩ := hck
      exact ⟨ck, h1, h2.mono (Trace.append_le tr _)⟩
  cks p st i hst := h.cks p st i (trStateStoredAt_append_other rfl hst)

private theorem rdec_sinv_append_st {tr : ExecTrace} {p₀ : Participant} {st₀ : TRState}
    (hrecv : ∀ c ∈ st₀.recv,
      ChainOKTR tr c.ratchetKey c.chainKey ∨
      ∃ ikA ikB pqpk opk t e,
        c.chainKey = (DY.Libsignal.PQXDH.aliceAgreement ikA (randTerm t 32) ikB c.ratchetKey pqpk opk e).2.ck)
    (hcks : CksOKTR st₀)
    (h : SInvTR tr) :
    SInvTR (tr.append (TRStE p₀ st₀)) where
  recv p st i hst c hc := by
    rcases trStateStoredAt_append_same hst with ⟨_, hst⟩ | ⟨_, _, rfl⟩
    · exact (h.recv p st i hst c hc).imp (fun h => h.mono (Trace.append_le tr _)) id
    · exact (hrecv c hc).imp (fun h => h.mono (Trace.append_le tr _)) id
  skip s pk n seed rIdx src j hl := by
    obtain ⟨ck, h1, h2⟩ := h.skip s pk n seed rIdx src j (eventLoggedAt_append_other rfl hl)
    exact ⟨ck, h1, h2.mono (Trace.append_le tr _)⟩
  cks p st i hst := by
    rcases trStateStoredAt_append_same hst with ⟨_, hst⟩ | ⟨_, _, rfl⟩
    · exact h.cks p st i hst
    · exact hcks

/-! ## Decrypt and parsing helpers -/

private theorem rdec_recvChainFor_false {st : DRState} {pk : DY.Bytes} {c : RecvChain}
    (h : recvChainFor st pk = some (c, false)) : c ∈ st.recv ∧ c.ratchetKey = pk := by
  unfold recvChainFor at h
  rcases hf : findRecvChain st.recv pk with _ | c'
  · rw [hf] at h; dsimp only at h
    split at h <;> cases h
  · rw [hf] at h; injection h with hp; injection hp with hc _
    subst hc
    unfold findRecvChain at hf
    exact ⟨List.mem_of_find?_eq_some hf, by simpa using List.find?_some hf⟩

theorem rdec_mem_setRecvChain {recv : List RecvChain} {c' x : RecvChain}
    (hx : x ∈ setRecvChain recv c') : x = c' ∨ x ∈ recv := by
  unfold setRecvChain at hx
  rw [List.mem_map] at hx
  obtain ⟨c, hc, rfl⟩ := hx
  split
  · exact .inl rfl
  · exact .inr hc

theorem rdec_consumeMessageKey_eq {c c' : RecvChain} {counter : UInt32} {seed : DY.Bytes}
    (h : consumeMessageKey c counter = some (seed, c')) :
    seed = (kdfCk (chainKeyAt c.chainKey (counter.toNat - c.index.toNat))).2 ∧
    c'.chainKey = (kdfCk (chainKeyAt c.chainKey (counter.toNat - c.index.toNat))).1 ∧
    c'.ratchetKey = c.ratchetKey := by
  unfold consumeMessageKey at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · injection h with hPair
        injection hPair with hs hC
        subst hs hC
        exact ⟨rfl, rfl, rfl⟩

theorem rdec_receiveSignalMsg_some {msgIdx : Nat} {tr : ExecTrace} {msg : TRSignalMsg}
    (h : ((DY.Libsignal.TripleRatchet.receiveSignalMsg msgIdx).run tr).1 = some msg) :
    ∃ t, t.AttackerKnows tr ∧ parseTrSignalMsg t = some msg := by
  unfold DY.Libsignal.TripleRatchet.receiveSignalMsg at h
  simp only [Symbolic.DYBridge.DY.Network.receiveMessage_eq_1,
    Symbolic.DYBridge.DY.getEntry_eq_1,
    Symbolic.DYBridge.DY.Traceful.mk_eq_1,
    Symbolic.DYBridge.DY.Traceful.run_eq_1] at h
  rcases hnet : (tr.at? msgIdx : Option NetEntry) with _ | ⟨raw⟩
  · simp only [hnet, Bind.bind] at h; cases h
  · simp only [hnet, Bind.bind, Pure.pure] at h
    rcases hparse : parseTrSignalMsg raw.msg with _ | m
    · rw [hparse] at h; cases h
    · rw [hparse] at h; dsimp only at h; unfold _root_.guard at h; split at h
      · cases h
      · injection h with hmsg; subst hmsg
        exact ⟨raw.msg, NetMsgAt.attackerKnows hnet, hparse⟩

theorem rdec_ratchetKey_known_of_parse {t : DY.Bytes} {msg : TRSignalMsg} {tr : ExecTrace}
    (ht : t.AttackerKnows tr) (hparse : parseTrSignalMsg t = some msg) :
    msg.ratchetKey.AttackerKnows tr := by
  obtain ⟨x₀, hsplit, _hx₀, hpack, hrk_eq, _hct_eq, _hpq_eq⟩ := parseTrSignalMsg_unpack hparse
  have hsp_ak := Concat.attacker_knows_split t (t.length - Trunc.trunc8Length) tr ht
  rw [hsplit] at hsp_ak
  have hwire_ak : msg.wire.AttackerKnows tr := hsp_ak.1
  rw [hpack] at hwire_ak
  have htrw : x₀.pack = DY.TrWire.trWireMsg x₀.version x₀.senderRatchetKey x₀.counter
      x₀.previousCounter x₀.ciphertext x₀.pqRatchet x₀.encodingVariation := rfl
  rw [htrw] at hwire_ak
  rw [hrk_eq]
  exact (DY.TrWire.attacker_knows_trWireMsg_args _ _ _ _ _ _ _ tr hwire_ak).1

theorem rdec_verifyMacAndDecrypt_some {st : TRState} {msg : TRSignalMsg}
    {pqSalt seed m : DY.Bytes} {tr : ExecTrace}
    (h : ((DY.Libsignal.TripleRatchet.verifyMacAndDecrypt st msg pqSalt seed).run tr).1 = some m) :
    msg.mac = computeMac (trMsgKeys pqSalt seed).macKey st.peerIk st.myIk msg.wire := by
  unfold DY.Libsignal.TripleRatchet.verifyMacAndDecrypt at h
  simp only [_root_.guard, Traceful.run_bind] at h
  by_contra hne
  simp [hne, Traceful.run_failure] at h

/-! ## Fresh-chain knowledge on the pre-trace -/

private theorem rdec_stored_dhs_rand {tr : ExecTrace} (hD : CompDhsOriginInv tr)
    {p : Participant} {st : TRState} {i : Nat} (hst : TRStateStoredAt p st i tr) :
    ∃ t : Nat, st.dhs = randTerm t 32 := by
  obtain ⟨t, _, ht⟩ := hD.dhs_rand st.dhs (st.sessionInfo p) st.rIdx (.inl ⟨st, i, hst, rfl, rfl, rfl⟩)
  exact ⟨t, ht⟩

private theorem rdec_chainOK_createChain_known {tr : ExecTrace} {pk₀ rk pk : DY.Bytes} {t₀ m : Nat}
    (hj : LitJunk pk) (h : ChainOKTR tr pk₀ (chainKeyAt (createChain rk pk (randTerm t₀ 32)).2 m)) :
    (createChain rk pk (randTerm t₀ 32)).2.AttackerKnows tr := by
  obtain ⟨b, k, hck, hg, hb⟩ := h
  obtain ⟨_, hb_eq⟩ := chainKeyAt_base_inj_tr (.inr (.inl ⟨rk, t₀, rfl⟩)) hb hck.symm
  rcases hb with ⟨i, n, rfl⟩ | ⟨rk', t', rfl⟩ | ⟨ikA, ikB, pqpk, opk, t', e, rfl⟩
  · exact absurd hb_eq (rdec_randTerm_ne_createChain_snd i n rk pk (randTerm t₀ 32))
  · obtain ⟨_, hx, _⟩ := createChain_snd_litJunk_tr hj hb_eq
    rw [← hb_eq]
    exact (hg (rdec_litJunk_of_x25519Key_eq hj hx)).2
  · exact absurd hb_eq (pqxdhKdf_ck_ne_createChain_snd _ rk pk (randTerm t₀ 32))

private theorem rdec_chainOK_alice_known {tr : ExecTrace}
    {pk₀ ikA ikB pk pqpk e : DY.Bytes} {opk : Option DY.Bytes} {t₀ m : Nat}
    (hj : LitJunk pk)
    (h : ChainOKTR tr pk₀ (chainKeyAt (DY.Libsignal.PQXDH.aliceAgreement ikA (randTerm t₀ 32) ikB pk pqpk opk e).2.ck m)) :
    (DY.Libsignal.PQXDH.aliceAgreement ikA (randTerm t₀ 32) ikB pk pqpk opk e).2.ck.AttackerKnows tr := by
  obtain ⟨b, k, hck, hg, hb⟩ := h
  obtain ⟨_, hb_eq⟩ := chainKeyAt_base_inj_tr (.inr (.inr ⟨ikA, ikB, pqpk, opk, t₀, e, rfl⟩)) hb hck.symm
  rcases hb with ⟨i, n, rfl⟩ | ⟨rk', t', rfl⟩ | ⟨ikA', ikB', pqpk', opk', t', e', rfl⟩
  · exact absurd hb_eq (rdec_randTerm_ne_pqxdhKdf_ck i n _)
  · exact absurd hb_eq.symm (pqxdhKdf_ck_ne_createChain_snd _ rk' pk₀ (randTerm t' 32))
  · obtain ⟨hx, _⟩ := aliceAgreement_ck_litJunk_tr hj hb_eq
    rw [← hb_eq]
    exact (hg (rdec_litJunk_of_x25519Key_eq hj hx)).2

private theorem rdec_stepdown {tr₀ : ExecTrace} (hCk : CkKnownCasesTRP)
    (hreach : ReachableTrace tr₀) (hI : SInvTR tr₀)
    (hD : CompDhsOriginInv tr₀)
    (hDep : ∀ p st i, TRStateStoredAt p st i tr₀ → saltDepth st.rk = 2 * st.rIdx + 2)
    {p₀ : Participant} {st₀ : TRState} {i₀ : Nat} (hst₀ : TRStateStoredAt p₀ st₀ i₀ tr₀)
    {pk : DY.Bytes} (hj : LitJunk pk) :
    ∀ n, (chainKeyAt (createChain st₀.rk pk st₀.dhs).2 n).AttackerKnows tr₀ →
      (createChain st₀.rk pk st₀.dhs).2.AttackerKnows tr₀
  | 0, h => h
  | n + 1, h => by
    rw [chainKeyAt_succ_eq_kdfCk_fst] at h
    rcases hCk hreach h with h' | ⟨p, st, i, hst, hs⟩
    · exact rdec_stepdown hCk hreach hI hD hDep hst₀ hj n h'
    · obtain ⟨t₀, ht₀⟩ := rdec_stored_dhs_rand hD hst₀
      rcases hs with hcks | ⟨c, hc, hcc⟩
      · exfalso
        rcases hI.cks p st i hst with ⟨i', n', k, hk⟩ | ⟨rk', pk', k, hk, hr⟩
        · rw [hk, ← chainKeyAt_succ_eq_kdfCk_fst, ht₀] at hcks
          obtain ⟨_, hb_eq⟩ :=
            chainKeyAt_base_inj_tr (pk' := pk) (.inr (.inl ⟨st₀.rk, t₀, rfl⟩)) (.inl ⟨i', n', rfl⟩) hcks
          exact rdec_randTerm_ne_createChain_snd i' n' st₀.rk pk (randTerm t₀ 32) hb_eq
        · obtain ⟨t, ht⟩ := rdec_stored_dhs_rand hD hst
          rw [hk, ← chainKeyAt_succ_eq_kdfCk_fst, ht, ht₀] at hcks
          obtain ⟨_, hb⟩ :=
            chainKeyAt_base_inj_tr (.inr (.inl ⟨st₀.rk, t₀, rfl⟩)) (.inr (.inl ⟨rk', t, rfl⟩)) hcks
          obtain ⟨hrk', _, hdhs_rand⟩ := createChain_snd_litJunk_tr hj hb
          have hdhs : st.dhs = st₀.dhs := by rw [ht, ht₀, hdhs_rand]
          have hsd : saltDepth st.rk = saltDepth st₀.rk + 2 := by
            rw [hr, saltDepth_createChain_fst, hrk']
          have d1 : saltDepth st.rk = 2 * st.rIdx + 2 := hDep p st i hst
          have d0 : saltDepth st₀.rk = 2 * st₀.rIdx + 2 := hDep p₀ st₀ i₀ hst₀
          have hu := hD.dhs_unique st.dhs (st.sessionInfo p) st.rIdx (st₀.sessionInfo p₀) st₀.rIdx
            (.inl ⟨st, i, hst, rfl, rfl, rfl⟩) (.inl ⟨st₀, i₀, hst₀, rfl, hdhs.symm, rfl⟩)
          omega
      · rcases hI.recv p st i hst c hc with hok | ⟨ikA, ikB, pqpk, opk, t, e, hck_eq⟩
        · rw [hcc, ← chainKeyAt_succ_eq_kdfCk_fst, ht₀] at hok
          rw [ht₀]
          exact rdec_chainOK_createChain_known hj hok
        · exact False.elim (isChainRoot_pqxdhKdf_ck _ _ (hck_eq.symm.trans hcc))

private theorem rdec_freshSeed {tr₀ : ExecTrace} (hCk : CkKnownCasesTRP)
    (hreach : ReachableTrace tr₀) (hI : SInvTR tr₀)
    (hD : CompDhsOriginInv tr₀)
    (hDep : ∀ p st i, TRStateStoredAt p st i tr₀ → saltDepth st.rk = 2 * st.rIdx + 2)
    {p₀ : Participant} {st₀ : TRState} {i₀ : Nat} (hst₀ : TRStateStoredAt p₀ st₀ i₀ tr₀)
    {pk : DY.Bytes} (hj : LitJunk pk) (n : Nat)
    (h : (kdfCk (chainKeyAt (createChain st₀.rk pk st₀.dhs).2 n)).2.AttackerKnows tr₀) :
    (createChain st₀.rk pk st₀.dhs).2.AttackerKnows tr₀ := by
  rcases seedKnownCasesTR hreach h with h' | ⟨j, ses, pk', n', rIdx, src, hl⟩
  · exact rdec_stepdown hCk hreach hI hD hDep hst₀ hj n h'
  · obtain ⟨ck, hseed, hok⟩ := hI.skip _ _ _ _ _ _ _ hl
    obtain ⟨t₀, ht₀⟩ := rdec_stored_dhs_rand hD hst₀
    rw [← rdec_kdfCk_snd_inj hseed, ht₀] at hok
    rw [ht₀]
    exact rdec_chainOK_createChain_known hj hok

private theorem rdec_stepdown_of_ne_dhs {tr₀ : ExecTrace} (hCk : CkKnownCasesTRP)
    (hreach : ReachableTrace tr₀) (hI : SInvTR tr₀) (hD : CompDhsOriginInv tr₀)
    {rk₀ pk : DY.Bytes} {t₀ : Nat}
    (hne : ∀ p st i, TRStateStoredAt p st i tr₀ → st.dhs ≠ randTerm t₀ 32)
    (hj : LitJunk pk) :
    ∀ n, (chainKeyAt (createChain rk₀ pk (randTerm t₀ 32)).2 n).AttackerKnows tr₀ →
      (createChain rk₀ pk (randTerm t₀ 32)).2.AttackerKnows tr₀
  | 0, h => h
  | n + 1, h => by
    rw [chainKeyAt_succ_eq_kdfCk_fst] at h
    rcases hCk hreach h with h' | ⟨p, st, i, hst, hs⟩
    · exact rdec_stepdown_of_ne_dhs hCk hreach hI hD hne hj n h'
    · rcases hs with hcks | ⟨c, hc, hcc⟩
      · exfalso
        rcases hI.cks p st i hst with ⟨i', n', k, hk⟩ | ⟨rk', pk', k, hk, _⟩
        · rw [hk, ← chainKeyAt_succ_eq_kdfCk_fst] at hcks
          obtain ⟨_, hb_eq⟩ :=
            chainKeyAt_base_inj_tr (pk' := pk) (.inr (.inl ⟨rk₀, t₀, rfl⟩)) (.inl ⟨i', n', rfl⟩) hcks
          exact rdec_randTerm_ne_createChain_snd i' n' rk₀ pk (randTerm t₀ 32) hb_eq
        · obtain ⟨t, ht⟩ := rdec_stored_dhs_rand hD hst
          rw [hk, ← chainKeyAt_succ_eq_kdfCk_fst, ht] at hcks
          obtain ⟨_, hb⟩ :=
            chainKeyAt_base_inj_tr (.inr (.inl ⟨rk₀, t₀, rfl⟩)) (.inr (.inl ⟨rk', t, rfl⟩)) hcks
          obtain ⟨_, _, hdhs_rand⟩ := createChain_snd_litJunk_tr hj hb
          exact hne p st i hst (ht.trans hdhs_rand)
      · rcases hI.recv p st i hst c hc with hok | ⟨ikA, ikB, pqpk, opk, t, e, hck_eq⟩
        · rw [hcc, ← chainKeyAt_succ_eq_kdfCk_fst] at hok
          exact rdec_chainOK_createChain_known hj hok
        · exact False.elim (isChainRoot_pqxdhKdf_ck _ _ (hck_eq.symm.trans hcc))

theorem rdec_freshSeed_of_ne_dhs {tr₀ : ExecTrace} (hCk : CkKnownCasesTRP)
    (hreach : ReachableTrace tr₀) (hI : SInvTR tr₀)
    {rk₀ pk : DY.Bytes} {t₀ : Nat}
    (hne : ∀ p st i, TRStateStoredAt p st i tr₀ → st.dhs ≠ randTerm t₀ 32)
    (hj : LitJunk pk) (n : Nat)
    (h : (kdfCk (chainKeyAt (createChain rk₀ pk (randTerm t₀ 32)).2 n)).2.AttackerKnows tr₀) :
    (createChain rk₀ pk (randTerm t₀ 32)).2.AttackerKnows tr₀ := by
  have hD : CompDhsOriginInv tr₀ := compDhsOriginInv_reachable hreach
  rcases seedKnownCasesTR hreach h with h' | ⟨j, ses, pk', n', rIdx, src, hl⟩
  · exact rdec_stepdown_of_ne_dhs hCk hreach hI hD hne hj n h'
  · obtain ⟨ck, hseed, hok⟩ := hI.skip _ _ _ _ _ _ _ hl
    rw [← rdec_kdfCk_snd_inj hseed] at hok
    exact rdec_chainOK_createChain_known hj hok

private theorem rdec_stepdown_alice {tr₀ : ExecTrace} (hCk : CkKnownCasesTRP)
    (hreach : ReachableTrace tr₀) (hI : SInvTR tr₀) (hD : CompDhsOriginInv tr₀)
    {ikA ikB pk pqpk e : DY.Bytes} {opk : Option DY.Bytes} {t₀ : Nat} (hj : LitJunk pk) :
    ∀ n, (chainKeyAt (DY.Libsignal.PQXDH.aliceAgreement ikA (randTerm t₀ 32) ikB pk pqpk opk e).2.ck n).AttackerKnows tr₀ →
      (DY.Libsignal.PQXDH.aliceAgreement ikA (randTerm t₀ 32) ikB pk pqpk opk e).2.ck.AttackerKnows tr₀
  | 0, h => h
  | n + 1, h => by
    rw [chainKeyAt_succ_eq_kdfCk_fst] at h
    rcases hCk hreach h with h' | ⟨p, st, i, hst, hs⟩
    · exact rdec_stepdown_alice hCk hreach hI hD hj n h'
    · rcases hs with hcks | ⟨c, hc, hcc⟩
      · exfalso
        rcases hI.cks p st i hst with ⟨i', n', k, hk⟩ | ⟨rk', pk', k, hk, _⟩
        · rw [hk, ← chainKeyAt_succ_eq_kdfCk_fst] at hcks
          obtain ⟨_, hb_eq⟩ := chainKeyAt_base_inj_tr (pk' := pk)
            (.inr (.inr ⟨ikA, ikB, pqpk, opk, t₀, e, rfl⟩)) (.inl ⟨i', n', rfl⟩) hcks
          exact rdec_randTerm_ne_pqxdhKdf_ck i' n' _ hb_eq
        · obtain ⟨t, ht⟩ := rdec_stored_dhs_rand hD hst
          rw [hk, ← chainKeyAt_succ_eq_kdfCk_fst, ht] at hcks
          obtain ⟨_, hb_eq⟩ := chainKeyAt_base_inj_tr
            (.inr (.inr ⟨ikA, ikB, pqpk, opk, t₀, e, rfl⟩)) (.inr (.inl ⟨rk', t, rfl⟩)) hcks
          exact pqxdhKdf_ck_ne_createChain_snd _ rk' pk' (randTerm t 32) hb_eq.symm
      · rcases hI.recv p st i hst c hc with hok | ⟨ikA', ikB', pqpk', opk', t', e', hck_eq⟩
        · rw [hcc, ← chainKeyAt_succ_eq_kdfCk_fst] at hok
          exact rdec_chainOK_alice_known hj hok
        · exact False.elim (isChainRoot_pqxdhKdf_ck _ _ (hck_eq.symm.trans hcc))

private theorem rdec_freshSeed_alice {tr₀ : ExecTrace} (hCk : CkKnownCasesTRP)
    (hreach : ReachableTrace tr₀) (hI : SInvTR tr₀) (hD : CompDhsOriginInv tr₀)
    {ikA ikB pk pqpk e : DY.Bytes} {opk : Option DY.Bytes} {t₀ : Nat} (hj : LitJunk pk) (n : Nat)
    (h : (kdfCk (chainKeyAt (DY.Libsignal.PQXDH.aliceAgreement ikA (randTerm t₀ 32) ikB pk pqpk opk e).2.ck n)).2.AttackerKnows tr₀) :
    (DY.Libsignal.PQXDH.aliceAgreement ikA (randTerm t₀ 32) ikB pk pqpk opk e).2.ck.AttackerKnows tr₀ := by
  rcases seedKnownCasesTR hreach h with h' | ⟨j, ses, pk', n', rIdx, src, hl⟩
  · exact rdec_stepdown_alice hCk hreach hI hD hj n h'
  · obtain ⟨ck, hseed, hok⟩ := hI.skip _ _ _ _ _ _ _ hl
    rw [← rdec_kdfCk_snd_inj hseed] at hok
    exact rdec_chainOK_alice_known hj hok

/-! ## Preservation of `SInvTR` across `messageDecrypt` -/

theorem rdec_logSkippedKeys_fst (s : SessionInfo) (pk : DY.Bytes) (rIdx src : Nat) :
    ∀ (ck : DY.Bytes) (n : UInt32) (k : Nat) (tr : ExecTrace),
      ((logSkippedKeys s pk rIdx src ck n k).run tr).1 = some ()
  | _, _, 0, _ => by simp only [logSkippedKeys, Symbolic.DYBridge.DY.Traceful.run_eq_1]; rfl
  | ck, n, k + 1, tr => by
    unfold logSkippedKeys
    rw [run_bind_fst]
    have hlf : ((ProtocolEvent.logEvent (TREvent.SkippedKeyStored s pk n (kdfCk ck).2 rIdx src)).run tr).1 = some () := by
      simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
        Symbolic.DYBridge.DY.appendEntry_eq_1,
        Symbolic.DYBridge.DY.Traceful.mk_eq_1,
        Symbolic.DYBridge.DY.Traceful.run_eq_1]
      rfl
    rw [hlf]; dsimp only
    exact rdec_logSkippedKeys_fst s pk rIdx src (kdfCk ck).1 (n + 1) k _

theorem rdec_logSkippedKeys_le (s : SessionInfo) (pk : DY.Bytes) (rIdx src : Nat) :
    ∀ (ck : DY.Bytes) (n : UInt32) (k : Nat) (tr : ExecTrace),
      tr ≤ ((logSkippedKeys s pk rIdx src ck n k).run tr).2.val
  | _, _, 0, tr => by
    simp only [logSkippedKeys, Symbolic.DYBridge.DY.Traceful.run_eq_1]
    exact Trace.le_refl tr
  | _, _, _ + 1, tr => ((logSkippedKeys _ _ _ _ _ _ _).run tr).2.property

theorem rdec_sinv_logSkippedKeys (s : SessionInfo) (pk : DY.Bytes) (rIdx src : Nat) :
    ∀ (ck : DY.Bytes) (n : UInt32) (k : Nat) (tr : ExecTrace), SInvTR tr → ChainOKTR tr pk ck →
      SInvTR ((logSkippedKeys s pk rIdx src ck n k).run tr).2.val
  | _, _, 0, _, h, _ => by
    simp only [logSkippedKeys, Symbolic.DYBridge.DY.Traceful.run_eq_1]
    exact h
  | ck, n, k + 1, tr, h, hck => by
    unfold logSkippedKeys
    rw [run_bind_snd]
    have hlf : ((ProtocolEvent.logEvent (TREvent.SkippedKeyStored s pk n (kdfCk ck).2 rIdx src)).run tr).1 = some () := by
      simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
        Symbolic.DYBridge.DY.appendEntry_eq_1,
        Symbolic.DYBridge.DY.Traceful.mk_eq_1,
        Symbolic.DYBridge.DY.Traceful.run_eq_1]
      rfl
    have hls : ((ProtocolEvent.logEvent (TREvent.SkippedKeyStored s pk n (kdfCk ck).2 rIdx src)).run tr).2.val =
        tr.append (TREvE (TREvent.SkippedKeyStored s pk n (kdfCk ck).2 rIdx src)) := by
      simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
        Symbolic.DYBridge.DY.appendEntry_eq_1,
        Symbolic.DYBridge.DY.Traceful.mk_eq_1,
        Symbolic.DYBridge.DY.Traceful.run_eq_1]
      rfl
    rw [hlf, hls]; dsimp only
    have h1 : SInvTR (tr.append
        (TREvE (TREvent.SkippedKeyStored s pk n (kdfCk ck).2 rIdx src))) :=
      rdec_sinv_append_skip ⟨ck, rfl, hck⟩ h
    have hle := Trace.append_le tr
      (TREvE (TREvent.SkippedKeyStored s pk n (kdfCk ck).2 rIdx src))
    exact rdec_sinv_logSkippedKeys s pk rIdx src (kdfCk ck).1 (n + 1) k _ h1
      ((rdec_chainOK_kdfCk_fst hck).mono hle)

private theorem rdec_sinv_decTail (me : Participant) (stH : Nat) (st : TRState) (msg : TRSignalMsg)
    (c c' : RecvChain) (seed pqSalt m spqr' : DY.Bytes) (tr : ExecTrace) (h : SInvTR tr)
    (hc : ChainOKTR tr msg.ratchetKey c.chainKey)
    (hc' : ChainOKTR tr c'.ratchetKey c'.chainKey)
    (hrecv : ∀ x ∈ st.recv,
      ChainOKTR tr x.ratchetKey x.chainKey ∨
      ∃ ikA ikB pqpk opk t e,
        x.chainKey = (DY.Libsignal.PQXDH.aliceAgreement ikA (randTerm t 32) ikB x.ratchetKey pqpk opk e).2.ck)
    (hcks : CksOKTR st) :
    SInvTR ((do
      logSkippedKeys (st.sessionInfo me) msg.ratchetKey c.rIdx stH c.chainKey c.index
        (msg.counter.toNat - c.index.toNat)
      ProtocolEvent.logEvent (TREvent.Received me st.peer msg.ratchetKey msg.counter m)
      logMessageKeyAndStore me (st.sessionInfo me) .receiver seed pqSalt msg.counter c.rIdx stH { st with recv := setRecvChain st.recv c', spqr := spqr' }).run tr).2.val := by
  rw [run_bind_snd, rdec_logSkippedKeys_fst]
  dsimp only
  let tr1 := ((logSkippedKeys (st.sessionInfo me) msg.ratchetKey c.rIdx stH c.chainKey c.index
    (msg.counter.toNat - c.index.toNat)).run tr).2.val
  have hle1 : tr ≤ tr1 := rdec_logSkippedKeys_le _ _ _ _ _ _ _ tr
  have h1 : SInvTR tr1 := rdec_sinv_logSkippedKeys _ _ _ _ _ _ _ tr h hc
  let tr2 := tr1.append
    (TREvE (TREvent.Received me st.peer msg.ratchetKey msg.counter m))
  have hle2 : tr1 ≤ tr2 := Trace.append_le tr1 _
  have h2 : SInvTR tr2 := rdec_sinv_append_tr (fun _ _ _ _ _ _ h => nomatch h) h1
  let ev := TREvent.MessageKey (st.sessionInfo me) .receiver seed pqSalt msg.counter c.rIdx stH
  let tr3 := tr2.append (TREvE ev)
  have hle3 : tr2 ≤ tr3 := Trace.append_le tr2 _
  have h3 : SInvTR tr3 := rdec_sinv_append_tr (fun _ _ _ _ _ _ h => nomatch h) h2
  have hle13 : tr ≤ tr3 := Trace.le_trans _ _ _ hle1 (Trace.le_trans _ _ _ hle2 hle3)
  have htail_eq : ((do
      ProtocolEvent.logEvent (TREvent.Received me st.peer msg.ratchetKey msg.counter m)
      logMessageKeyAndStore me (st.sessionInfo me) .receiver seed pqSalt msg.counter c.rIdx stH { st with recv := setRecvChain st.recv c', spqr := spqr' }).run tr1).2.val =
      tr3.append (TRStE me { st with recv := setRecvChain st.recv c', spqr := spqr' }) := by
    unfold logMessageKeyAndStore
    simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
      Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
      Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
      Symbolic.DYBridge.DY.appendEntry_eq_1,
      Symbolic.DYBridge.DY.Traceful.mk_eq_1,
      Symbolic.DYBridge.DY.Traceful.run_eq_1]
    rfl
  rw [htail_eq]
  refine rdec_sinv_append_st (p₀ := me)
    (st₀ := { st with recv := setRecvChain st.recv c', spqr := spqr' })
    (fun x hx => ?_) hcks h3
  rcases rdec_mem_setRecvChain hx with rfl | hx
  · exact .inl (hc'.mono hle13)
  · exact (hrecv x hx).imp (fun h => h.mono hle13) id

private theorem rdec_run_sendMessage_bind_snd {α : Type} (m : DY.Bytes)
    (f : Nat → Traceful α) (tr : ExecTrace) :
    ((Network.sendMessage m >>= f).run tr).2.val = ((f tr.length).run (tr.append (NetE m))).2.val := by
  simp only [Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1,
    Symbolic.DYBridge.DY.Traceful.mk_eq_1,
    Symbolic.DYBridge.DY.Traceful.run_eq_1]
  rfl

theorem bind_ensureReceiverChain_tr {Inv : ExecTrace → Prop} {α : Type}
    (st₀ : TRState) (pk : DY.Bytes) (tr₀ : ExecTrace) (hInv₀ : Inv tr₀)
    {f : TRState × RecvChain × Bool → Traceful α}
    (hfalse : ∀ c, recvChainFor st₀.toDRState pk = some (c, false) →
      Inv ((f (st₀, c, false)).run tr₀).2.val)
    (htrue : ∀ c, recvChainFor st₀.toDRState pk = some (c, true) → (!x25519LowOrder pk) = true →
      let dhs := randTerm tr₀.length 32
      let c' : RecvChain := {
        ratchetKey := pk, chainKey := (createChain st₀.rk pk st₀.dhs).2, index := 0, rIdx := st₀.rIdx + 2 }
      let st : TRState := {
        st₀ with
        rk := (createChain (createChain st₀.rk pk st₀.dhs).1 pk dhs).1, dhs := dhs,
        cks := (createChain (createChain st₀.rk pk st₀.dhs).1 pk dhs).2, ns := 0,
        pn := if st₀.ns = 0 then 0 else st₀.ns - 1, rIdx := st₀.rIdx + 2,
        recv := (st₀.recv ++ [c']).drop ((st₀.recv.length + 1) - maxReceiverChains) }
      Inv ((f (st, c', true)).run (tr₀.append (RndE 32))).2.val) :
    Inv ((ensureReceiverChain st₀ pk >>= f).run tr₀).2.val := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]
  cases hrc : recvChainFor st₀.toDRState pk with
  | none => simp only [Symbolic.DYBridge.DY.Traceful.run_eq_1]; exact hInv₀
  | some p =>
    rcases p with ⟨c, false | true⟩
    · rw [run_pure_bind_snd]; exact hfalse c hrc
    · dsimp only
      rw [run_bind_assoc_snd]
      simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard]; unfold _root_.guard
      by_cases hlo : (!x25519LowOrder pk) = true
      · rw [ite_eq_left_iff.mpr fun h => absurd hlo h, run_bind_assoc_snd, run_pure_bind_snd]
        dsimp only
        rw [run_bind_assoc_snd, run_genRand_bind_snd, run_pure_bind_snd, run_pure_bind_snd]
        exact htrue c hrc hlo
      · rw [ite_eq_right_iff.mpr fun h => absurd h hlo]
        simp only [Symbolic.DYBridge.DY.Traceful.run_eq_1]
        exact hInv₀

/-- `TripleRatchet.messageDecrypt` preserves `SInvTR`, given `CkKnownCasesTRP` and `DepthTR` on `tr₀`. -/
theorem sinvTR_messageDecrypt (hCk : CkKnownCasesTRP)
    (me : Participant) (stH msgIdx pqIdx : Nat) (spqrMsgIdx : UInt32) (tr₀ : ExecTrace)
    (hreach : ReachableTrace tr₀) (hI : SInvTR tr₀)
    (hDep : ∀ p st i, TRStateStoredAt p st i tr₀ →
      saltDepth st.rk = 2 * st.rIdx + 2) :
    SInvTR ((DY.Libsignal.TripleRatchet.messageDecrypt me stH msgIdx pqIdx spqrMsgIdx).run tr₀).2.val := by
  have hD : CompDhsOriginInv tr₀ := compDhsOriginInv_reachable hreach
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]
  rw [run_bind_snd, getLocalState_tr_fst, getLocalState_tr_snd]
  rcases he : (tr₀.at? stH : Option TRStEntry) with _ | ⟨⟨p, st₀⟩⟩
  · exact hI
  dsimp only
  by_cases hp : p = me
  swap
  · simp only [hp, ↓reduceIte]
    exact hI
  subst hp
  simp only [↓reduceIte]
  have hst₀ : TRStateStoredAt p st₀ stH tr₀ := he
  rw [run_bind_snd, CompDhsHelpers.receiveSignalMsg_trace]
  rcases hrm : ((DY.Libsignal.TripleRatchet.receiveSignalMsg msgIdx).run tr₀).1 with _ | msg
  · exact hI
  obtain ⟨t, ht, hparse⟩ := rdec_receiveSignalMsg_some hrm
  dsimp only
  refine bind_ensureReceiverChain_tr (Inv := SInvTR) st₀ msg.ratchetKey tr₀ hI
    (fun c hrc => ?_) (fun _ _ _ => ?_)
  · -- existing chain (`ratcheted = false`)
    obtain ⟨hcmem, hck⟩ := rdec_recvChainFor_false hrc
    dsimp only
    rcases hcons : consumeMessageKey c msg.counter with _ | ⟨seed, c'⟩
    · simp only [Symbolic.DYBridge.DY.Traceful.run_eq_1]; exact hI
    dsimp only
    obtain ⟨hseed, hc'k, hc'r⟩ := rdec_consumeMessageKey_eq hcons
    rcases Spqr.spqrRecv st₀.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩
    · simp only [Symbolic.DYBridge.DY.Traceful.run_eq_1]; exact hI
    dsimp only
    let tr1 := tr₀.append (NetE key)
    have hle1 : tr₀ ≤ tr1 := Trace.append_le tr₀ _
    have h1 : SInvTR tr1 := rdec_sinv_append_other rfl rfl hI
    rw [rdec_run_sendMessage_bind_snd, run_bind_snd, receiveMessage_snd]
    rcases ((Network.receiveMessage pqIdx).run tr1).1 with _ | pqSalt
    · exact h1
    dsimp only
    rw [run_bind_snd, verifyMacAndDecrypt_trace]
    rcases hvm : ((DY.Libsignal.TripleRatchet.verifyMacAndDecrypt st₀ msg pqSalt seed).run tr1).1 with _ | m
    · exact h1
    have hmac := rdec_verifyMacAndDecrypt_some hvm
    have hc : ChainOKTR tr₀ msg.ratchetKey c.chainKey := by
      rcases hI.recv p st₀ stH hst₀ c hcmem with hc₀ | ⟨ikA, ikB, pqpk, opk, t₀, e, hck_eq⟩
      · rw [← hck]; exact hc₀
      · rw [hck] at hck_eq
        refine ⟨c.chainKey, 0, rfl, ?_, .inr (.inr ⟨ikA, ikB, pqpk, opk, t₀, e, hck_eq⟩)⟩
        intro hj
        have hpk_ak : msg.ratchetKey.AttackerKnows tr₀ := rdec_ratchetKey_known_of_parse ht hparse
        rw [hseed, hck_eq] at hmac
        have hseed_ak := seed_known_of_forgedMac_tr hreach ht hparse hmac hj
        rw [hck_eq]
        exact ⟨hpk_ak, rdec_freshSeed_alice hCk hreach hI hD hj _ hseed_ak⟩
    have hc' : ChainOKTR tr₀ c'.ratchetKey c'.chainKey := by
      rw [hc'k, hc'r, hck]; exact rdec_chainOK_kdfCk_fst (rdec_chainOK_chainKeyAt hc _)
    dsimp only
    exact rdec_sinv_decTail p stH st₀ msg c c' seed pqSalt m spqr' tr1 h1
      (hc.mono hle1) (hc'.mono hle1)
      (fun x hx => (hI.recv p st₀ stH hst₀ x hx).imp (fun h => h.mono hle1) id)
      (hI.cks p st₀ stH hst₀)
  · -- fresh chain (`ratcheted = true`)
    dsimp only
    let dhs := randTerm tr₀.length 32
    let c1 : RecvChain := {
      ratchetKey := msg.ratchetKey, chainKey := (createChain st₀.rk msg.ratchetKey st₀.dhs).2,
      index := 0, rIdx := st₀.rIdx + 2 }
    let st : TRState := {
      st₀ with
      rk := (createChain (createChain st₀.rk msg.ratchetKey st₀.dhs).1 msg.ratchetKey dhs).1, dhs := dhs,
      cks := (createChain (createChain st₀.rk msg.ratchetKey st₀.dhs).1 msg.ratchetKey dhs).2, ns := 0,
      pn := if st₀.ns = 0 then 0 else st₀.ns - 1, rIdx := st₀.rIdx + 2,
      recv := (st₀.recv ++ [c1]).drop ((st₀.recv.length + 1) - maxReceiverChains) }
    let tr1 := tr₀.append (RndE 32)
    have hle1 : tr₀ ≤ tr1 := Trace.append_le tr₀ _
    have h1 : SInvTR tr1 := rdec_sinv_append_other rfl rfl hI
    rcases hcons : consumeMessageKey c1 msg.counter with _ | ⟨seed, c'⟩
    · simp only [Symbolic.DYBridge.DY.Traceful.run_eq_1]; exact h1
    dsimp only
    obtain ⟨hseed, hc'k, hc'r⟩ := rdec_consumeMessageKey_eq hcons
    rcases Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩
    · simp only [Symbolic.DYBridge.DY.Traceful.run_eq_1]; exact h1
    dsimp only
    let tr2 := tr1.append (NetE key)
    have hle2 : tr1 ≤ tr2 := Trace.append_le tr1 _
    have h2 : SInvTR tr2 := rdec_sinv_append_other rfl rfl h1
    rw [rdec_run_sendMessage_bind_snd, run_bind_snd, receiveMessage_snd]
    rcases ((Network.receiveMessage pqIdx).run tr2).1 with _ | pqSalt
    · exact h2
    dsimp only
    rw [run_bind_snd, verifyMacAndDecrypt_trace]
    rcases hvm : ((DY.Libsignal.TripleRatchet.verifyMacAndDecrypt st msg pqSalt seed).run tr2).1 with _ | m
    · exact h2
    have hmac := rdec_verifyMacAndDecrypt_some hvm
    have hgood : GoodTR tr₀ msg.ratchetKey (createChain st₀.rk msg.ratchetKey st₀.dhs).2 := by
      intro hj
      have hpk_ak : msg.ratchetKey.AttackerKnows tr₀ := rdec_ratchetKey_known_of_parse ht hparse
      have hseed' : seed = (kdfCk (chainKeyAt (createChain st₀.rk msg.ratchetKey st₀.dhs).2
          (msg.counter.toNat - 0))).2 := hseed
      rw [hseed'] at hmac
      have hseed_ak : (kdfCk (chainKeyAt (createChain st₀.rk msg.ratchetKey st₀.dhs).2
          (msg.counter.toNat - 0))).2.AttackerKnows tr₀ :=
        seed_known_of_forgedMac_tr hreach ht hparse hmac hj
      exact ⟨hpk_ak, rdec_freshSeed hCk hreach hI hD hDep hst₀ hj _ hseed_ak⟩
    obtain ⟨t₀, ht₀⟩ := rdec_stored_dhs_rand hD hst₀
    have hc0 : ChainOKTR tr₀ msg.ratchetKey c1.chainKey :=
      ⟨_, 0, rfl, hgood, .inr (.inl ⟨st₀.rk, t₀, by dsimp only [c1]; rw [ht₀]⟩)⟩
    dsimp only
    let tr3 := tr2.append
      (TREvE (TREvent.DHRatchet p st.peer msg.ratchetKey (DY.DiffieHellman.dhPk st.dhs)))
    have hle3 : tr2 ≤ tr3 := Trace.append_le tr2 _
    have h3 : SInvTR tr3 := rdec_sinv_append_tr (fun _ _ _ _ _ _ h => nomatch h) h2
    let tr4 := tr3.append
      (TREvE (TREvent.HonestDH (st.sessionInfo p) st.dhs (st.rIdx - 2)))
    have hle4 : tr3 ≤ tr4 := Trace.append_le tr3 _
    have h4 : SInvTR tr4 := rdec_sinv_append_tr (fun _ _ _ _ _ _ h => nomatch h) h3
    have hle04 : tr₀ ≤ tr4 :=
      Trace.le_trans _ _ _ hle1 (Trace.le_trans _ _ _ hle2 (Trace.le_trans _ _ _ hle3 hle4))
    have hc4 : ChainOKTR tr4 msg.ratchetKey c1.chainKey := hc0.mono hle04
    have hc'4 : ChainOKTR tr4 c'.ratchetKey c'.chainKey := by
      rw [hc'k, hc'r]; exact rdec_chainOK_kdfCk_fst (rdec_chainOK_chainKeyAt hc4 _)
    have hrecv4 : ∀ x ∈ st.recv,
        ChainOKTR tr4 x.ratchetKey x.chainKey ∨
        ∃ ikA ikB pqpk opk t e,
          x.chainKey = (DY.Libsignal.PQXDH.aliceAgreement ikA (randTerm t 32) ikB x.ratchetKey pqpk opk e).2.ck := by
      intro x hx
      rcases List.mem_append.mp (List.mem_of_mem_drop hx) with hx0 | hxc
      · exact (hI.recv p st₀ stH hst₀ x hx0).imp (fun h => h.mono hle04) id
      · rw [List.mem_singleton] at hxc
        subst hxc
        exact .inl hc4
    have hcks : CksOKTR st := .inr ⟨(createChain st₀.rk msg.ratchetKey st₀.dhs).1, msg.ratchetKey, 0,
      rfl, rfl⟩
    have hlog_bind : ∀ {α : Type} (ev : TREvent) (k : Unit → Traceful α) (t0 : ExecTrace),
        ((ProtocolEvent.logEvent ev >>= k).run t0).2.val = ((k ()).run (t0.append (TREvE ev))).2.val :=
      fun ev k t0 => by
        simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
          Symbolic.DYBridge.DY.appendEntry_eq_1,
          Symbolic.DYBridge.DY.Traceful.mk_eq_1,
          Symbolic.DYBridge.DY.Traceful.run_eq_1]
        rfl
    simp only [↓reduceIte]
    rw [hlog_bind, hlog_bind]
    exact rdec_sinv_decTail p stH st msg c1 c' seed pqSalt m spqr' tr4 h4 hc4 hc'4 hrecv4 hcks

end Symbolic.Swarm.CREF.TR.G1
