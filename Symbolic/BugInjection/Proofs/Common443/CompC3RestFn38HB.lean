/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.CompC3RestFn38HBA
public import Symbolic.BugInjection.Proofs.Common443.CompC3RestPre38HB
import Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse
import Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsTrue

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 200000
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Common443.CompC3RestFn38HB
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.Refinement (sha256CompressFunction shaStateBytes shaStateOfBytes torsionShift)
open Symbolic.BugInjection.Proofs.Common443.CompExcuse (trStatePrefixes)
open ByteSpecs DY DY.Libsignal DY.Libsignal.HwEvents DY.Libsignal.Composed DY.Libsignal.Composed.Refinement Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Proofs.Common443.CompExcuse Symbolic.BugInjection.Proofs.Common443.CompFreshDistinct Symbolic.BugInjection.Proofs.Common443.CompPlant Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice Symbolic.BugInjection.Proofs.Common443.CompPrefixInvBundle Symbolic.BugInjection.Proofs.Common443.CompPrefixInvEnc Symbolic.BugInjection.Proofs.Common443.CompPrefixInvStruct Symbolic.BugInjection.Proofs.Common443.CompPrefixInvSwap Symbolic.BugInjection.Proofs.Common443.CompRMemoKnown Symbolic.BugInjection.Proofs.Common443.CompRNoBSC Symbolic.BugInjection.Proofs.Common443.CompRPlantWire Symbolic.BugInjection.Proofs.Common443.CompRX0SS38 Symbolic.BugInjection.Proofs.Common443.CompRX0NBSC38 Symbolic.BugInjection.Proofs.Common443.CompRX0NBSC38Hmc Symbolic.BugInjection.Proofs.Common443.CompRX0NBSC38Parts Symbolic.BugInjection.Proofs.Common443.CompRX0NBSC38Wire Symbolic.BugInjection.Proofs.Common443.CompRX0Top Symbolic.BugInjection.Proofs.Common443.CompRTag Symbolic.BugInjection.Proofs.Common443.CompRI0TermInj Symbolic.BugInjection.Proofs.Common443.CompRNbscTable Symbolic.BugInjection.Proofs.Common443.CompRNbsc38MacKey Symbolic.BugInjection.Proofs.Common443.CompRNbsc38MacKeyWire Symbolic.BugInjection.Proofs.Common443.CompRSplit38Untagged Symbolic.BugInjection.Proofs.Common443.CompRSplit38ZPin Symbolic.BugInjection.Proofs.Common443.CompRSplit38ZTag Symbolic.BugInjection.Proofs.Common443.CompRSplit38ZVals Symbolic.BugInjection.Proofs.Common443.CompRSplit38PairCore Symbolic.BugInjection.Proofs.Common443.CompRSplit38UntaggedShape Symbolic.BugInjection.Proofs.Common443.CompRNonInj38Census Symbolic.BugInjection.Proofs.Common443.CompRQRestCensusZ Symbolic.BugInjection.Proofs.Common443.CompC2RestCore Symbolic.BugInjection.Proofs.Common443.CompC2Rest38 Symbolic.BugInjection.Proofs.Common443.CompC2RestFn Symbolic.BugInjection.Proofs.Common443.CompRWSBobChain Symbolic.BugInjection.Proofs.Common443.CompSetupSecrecy Symbolic.BugInjection.Proofs.Common443.CompC2PreUntagged38 Symbolic.BugInjection.Proofs.Common443.CompC3RestFn38HBA Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompTrace
abbrev Rest38FnHB : Prop := Rest38FnAt Witnesses.Cheval26SmallSubgroupHighBitComp.setup (Witnesses.Cheval26SmallSubgroupHighBitComp.trace.take 38) highBitWireBytes 1 0
abbrev Rest38FnTC : Prop := Rest38FnAt Witnesses.Cheval26SmallSubgroupTorsionComp.setup (Witnesses.Cheval26SmallSubgroupTorsionComp.trace.take 38) torsionWireBytes 0 1
section NRSt
variable {S : Sem} {g : Ghost}
def rTerms38 (tr₁ tr₂ : ExecTrace) (b : DY.Participant) (o : DY.Libsignal.PQXDH.AliceHandshakeOut) (cl : Nat) : List DY.Bytes :=
  let stA := iniAliceStartState tr₁ b o;
  [ randTerm 0 32, randTerm 5 32, randTerm 10 32, randTerm 16 64, randTerm tr₁.length 32, randTerm (tr₁.length + 1) 32, randTerm (tr₁.length + 2) 32, randTerm tr₂.length 32, randTerm (tr₂.length + 1) cl, DY.SymEnc.symEnc (encKeys tr₂ stA cl (tr₂.length + 2)).cipherKey (encKeys tr₂ stA cl (tr₂.length + 2)).iv (randTerm tr₂.length 32), (DY.PQKem.kemEncap (DY.PQKem.kemPk (randTerm 16 64)) (randTerm (tr₁.length + 1) 32)).1, (DY.PQKem.kemEncap (DY.PQKem.kemPk (randTerm 16 64)) (randTerm (tr₁.length + 1) 32)).2 ]
def allTerms38 (tr₁ tr₂ : ExecTrace) (b : DY.Participant) (o : DY.Libsignal.PQXDH.AliceHandshakeOut) (cl : Nat) : List DY.Bytes :=
  let stA := iniAliceStartState tr₁ b o;
  rTerms38 tr₁ tr₂ b o cl ++ [ DY.DiffieHellman.dhPk (randTerm 0 32), DY.DiffieHellman.dhPk (randTerm 5 32), DY.DiffieHellman.dhPk (randTerm 10 32), DY.DiffieHellman.dhPk (randTerm tr₁.length 32), DY.DiffieHellman.dhPk (randTerm (tr₁.length + 2) 32), DY.Libsignal.PQXDH.agree (DY.DiffieHellman.dhPk (randTerm 10 32)) (randTerm 0 32), DY.Libsignal.PQXDH.agree (DY.DiffieHellman.dhPk (randTerm 5 32)) (randTerm tr₁.length 32), DY.Libsignal.PQXDH.agree (DY.DiffieHellman.dhPk (randTerm 10 32)) (randTerm tr₁.length 32), DY.Libsignal.PQXDH.agree (DY.DiffieHellman.dhPk (randTerm 10 32)) (randTerm (tr₁.length + 2) 32), encMac tr₂ stA cl (tr₂.length + 2), DY.Trunc.trunc8 (zfullT tr₂ stA cl (tr₂.length + 2)) ]
abbrev FnCensus38 (tr₁ tr₂ : ExecTrace) (b : DY.Participant) (o : DY.Libsignal.PQXDH.AliceHandshakeOut) (cl : Nat) (S : Sem) (g : Ghost) (t : DY.Bytes) : Prop := FnCensus (allTerms38 tr₁ tr₂ b o cl) (rTerms38 tr₁ tr₂ b o cl) S g t
theorem nrcensus_randTerm38 {tr₁ tr₂ : ExecTrace} {b : DY.Participant} {o : DY.Libsignal.PQXDH.AliceHandshakeOut} {cl ts sz : Nat} (hmR : randTerm ts sz ∈ rTerms38 tr₁ tr₂ b o cl) : FnCensus38 tr₁ tr₂ b o cl S g (randTerm ts sz) := nrcensus_randTerm (List.mem_append_left _ hmR) hmR
theorem nrcensus_symEnc38 {tr₁ tr₂ : ExecTrace} {b : DY.Participant} {o : DY.Libsignal.PQXDH.AliceHandshakeOut} {cl : Nat} {k iv m : DY.Bytes} (hmR : DY.SymEnc.symEnc k iv m ∈ rTerms38 tr₁ tr₂ b o cl) (hk : FnCensus38 tr₁ tr₂ b o cl S g k) (hiv : FnCensus38 tr₁ tr₂ b o cl S g iv) (hm : FnCensus38 tr₁ tr₂ b o cl S g m) : FnCensus38 tr₁ tr₂ b o cl S g (DY.SymEnc.symEnc k iv m) := nrcensus_symEnc (List.mem_append_left _ hmR) hmR hk hiv hm
theorem gamma_setup_len {r : Records} (hc : Compat compI0 r S g) (hwf : RecordsWF r) {ts sz : Nat} (hp : (ts, sz) ∈ setupRandomsAt r) (hsz : sz ≠ 0) : (gamma compI0 S g (randTerm ts sz)).length = sz := by rw [CompPlant.gamma_randTerm_length compI0 S g ts sz hsz, hc.1 (ts, sz) hp]; exact hwf.2.1 (ts, sz) hp
theorem nrcensus_storedSecrets_hb {w : PQXDHSpqrSetup} {r : Records} {ms : List Move} {tr₁ tr₂ : ExecTrace} {b : DY.Participant} {o : DY.Libsignal.PQXDH.AliceHandshakeOut} {cl : Nat} (hfitsP : compFitsPinned w compI0 r) (hc : Compat compI0 r S g) (hns : ∀ m ∈ ms, m.isSetup = false) (hreach : (runTraceMoves r ms).Reachable DY.Libsignal.Composed.reachability) : ∀ u ∈ storedSecrets (runTraceMoves r ms), FnCensus38 tr₁ tr₂ b o cl S g u := by
  have hfits : compFits w compI0 r := CompFitsNames.compFits_base hfitsP; have hNe : r.alice ≠ r.bob := hfits.1.1; have hopk : r.withOpk = false := hfits.2.1; have hwf : RecordsWF r := hfits.1; have hA : r.alice = "alice" := CompFitsNames.compFits_alice hfitsP; have hB : r.bob = "bob" := CompFitsNames.compFits_bob hfitsP; have hinv := CompInv.spqrInv_of_reachable (runTraceMoves r ms) hreach; intro u hu; obtain ⟨j, _, ⟨part, kind, sk⟩, hat, rfl⟩ := CompRX0NBSC38Parts.mem_storedSecrets_iff.mp hu; have hkind : CompInv.KindOK (runTraceMoves r ms) part ⟨kind, sk⟩ := hinv.stOK part ⟨kind, sk⟩ j hat; dsimp only [CompInv.KindOK] at hkind
  have h32 {idx : Nat} (hr : randTerm idx 32 ∈ rTerms38 tr₁ tr₂ b o cl) (hs : (idx, 32) ∈ setupRandomsAt r) :
      FnCensus38 tr₁ tr₂ b o cl S g (randTerm idx 32) ∧ ((gamma compI0 S g (randTerm idx 32)).length = 32 ∨ (gamma compI0 S g (randTerm idx 32)).length = 64) :=
    ⟨nrcensus_randTerm38 hr, Or.inl (gamma_setup_len hc hwf hs (by decide))⟩
  cases kind with
  | identity =>
    rcases CompSetupSecrecy.ikAt_cases_of_no_setup hNe hns hkind with ⟨hp, rfl, _⟩ | ⟨hp, rfl, _⟩
    · have ⟨h1, h2⟩ := h32 (by simp [rTerms38]) (CompPrefixInvFresh.mem_setupRandomsAt_32 hNe (.inl (.inl rfl)))
      refine nrcensus_serialize_local_pqxdh (Or.inl (hp.trans hA)) ?_ ?_ <;> dsimp only <;> rw [CompSetupSecrecy.setupSecret_0 hNe] <;> [exact h1; exact h2]
    · have ⟨h1, h2⟩ := h32 (by simp [rTerms38]) (CompPrefixInvFresh.mem_setupRandomsAt_32 hNe (.inl (.inr (.inl rfl))))
      refine nrcensus_serialize_local_pqxdh (Or.inr (hp.trans hB)) ?_ ?_ <;> dsimp only <;> rw [CompSetupSecrecy.setupSecret_1 hNe] <;> [exact h1; exact h2]
  | signedPrekey =>
    obtain ⟨hp, rfl, _⟩ := CompSetupSecrecy.spkAt_eq_of_no_setup hNe hns hkind; have ⟨h1, h2⟩ := h32 (by simp [rTerms38]) (CompPrefixInvFresh.mem_setupRandomsAt_32 hNe (.inl (.inr (.inr rfl))))
    refine nrcensus_serialize_local_pqxdh (Or.inr (hp.trans hB)) ?_ ?_ <;> dsimp only <;> rw [CompSetupSecrecy.setupSecret_2 hNe] <;> [exact h1; exact h2]
  | pqPrekey =>
    obtain ⟨hp, rfl, _⟩ := CompSetupSecrecy.pqAt_eq_of_no_setup hNe hns hkind
    refine nrcensus_serialize_local_pqxdh (Or.inr (hp.trans hB)) ?_ ?_ <;> dsimp only <;> rw [CompSetupSecrecy.setupSecret_4 hNe]
    · exact nrcensus_randTerm38 (by simp [rTerms38])
    · exact Or.inr (gamma_setup_len hc hwf (CompPrefixInvFresh.mem_setupRandomsAt_64 r hNe (by simp)) (by decide))
  | oneTimePrekey =>
    obtain ⟨t, rfl, _, hev⟩ := hkind
    rcases CompSetupSecrecy.setupTrace_eventLoggedAt_cases hNe (CompSetupSecrecy.noNewNonMovePQEv_runTrace r ms hns _ (t + 1) rfl hev) with
      ⟨_, heq⟩ | ⟨_, heq⟩ | ⟨_, heq⟩ | ⟨_, heq⟩ | ⟨hopk_true, _, _⟩ <;> [cases heq; cases heq; cases heq; cases heq; (rw [hopk] at hopk_true; cases hopk_true)]
structure TRStateNRC (allT rT : List DY.Bytes) (S : Sem) (g : Ghost) (st : DY.Libsignal.TripleRatchet.TRState) : Prop where
  peer : st.peer = "alice" ∨ st.peer = "bob"
  myIk : FnCensus allT rT S g st.myIk
  peerIk : FnCensus allT rT S g st.peerIk
  rk : FnCensus allT rT S g st.rk
  dhs : FnCensus allT rT S g st.dhs
  cks : FnCensus allT rT S g st.cks
  ns_val : st.ns = 0 ∨ st.ns = 1
  pn_val : st.pn = 0
  sid : FnCensus allT rT S g st.sid
  spqr : FnCensus allT rT S g st.spqr
  recv : FnCensus allT rT S g ((Comparse.ExtensibleMessageFormat.list (Comparse.ParseableSerializeableNE.mf (a := DY.Libsignal.TripleRatchet.RecvChain))).serialize st.recv)
  recvT : KdfTail6 (gamma compI0 S g ((Comparse.ExtensibleMessageFormat.list (Comparse.ParseableSerializeableNE.mf (a := DY.Libsignal.TripleRatchet.RecvChain))).serialize st.recv))
  myIkL : (gamma compI0 S g st.myIk).length = 33
  peerIkL : (gamma compI0 S g st.peerIk).length = 33
theorem nrcensus_mem_trStatePrefixes {allT rT : List DY.Bytes} {ls : DY.PersistentLocalState.LocalState DY.Libsignal.TripleRatchet.TRState} (hpa : ls.participant = "alice" ∨ ls.participant = "bob") (hst : TRStateNRC allT rT S g ls.state) {p : DY.Bytes} (hp : p ∈ trStatePrefixes ls) : FnCensus allT rT S g p := by
  unfold trStatePrefixes at hp; simp only [List.mem_append] at hp
  rcases hp with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13
  · exact nrcensus_mem_slowString_participant hpa h1
  · exact nrcensus_mem_slowString_participant hst.peer h2
  · exact nrcensus_mem_slowBytes hst.myIk h3
  · exact nrcensus_mem_slowBytes hst.peerIk h4
  · exact nrcensus_mem_slowBytes hst.rk h5
  · exact nrcensus_mem_slowBytes hst.dhs h6
  · exact nrcensus_mem_slowBytes hst.cks h7
  · exact (nrcensus_mem_uint32_01 hst.ns_val h8).1
  · exact (nrcensus_mem_uint32_01 (Or.inl hst.pn_val) h9).1
  · exact nrcensus_mem_slowBytes hst.sid h10
  · exact nrcensus_mem_bool _ h11
  · exact nrcensus_mem_slowNat _ h12
  · exact nrcensus_mem_slowBytes hst.spqr h13
theorem nrcensus_serialize_local_tr {allT rT : List DY.Bytes} {ls : DY.PersistentLocalState.LocalState DY.Libsignal.TripleRatchet.TRState} (hpa : ls.participant = "alice" ∨ ls.participant = "bob") (hst : TRStateNRC allT rT S g ls.state) : FnCensus allT rT S g (Comparse.serialize ls : DY.Bytes) := by
  have hser : (Comparse.serialize ls : DY.Bytes) = Comparse.concatPrefixes (trStatePrefixes ls) ((Comparse.ExtensibleMessageFormat.list (Comparse.ParseableSerializeableNE.mf (a := DY.Libsignal.TripleRatchet.RecvChain))).serialize ls.state.recv) := by
    rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.serialize_local_tr_eq_bridge ls]
    simp only [trStatePrefixes, ← CompExcuse.concatPrefixes_append]
  rw [hser]; exact (nrcensus_concatPrefixes_kdfTail6 _ (fun _ hp => nrcensus_mem_trStatePrefixes hpa hst hp) hst.recv hst.recvT).1
theorem compKyberEncaps_drop1568_length' (b : HwBytes) : ((compKyberEncaps b).drop 1568).length = 32 := by
  have hL : (compKyberEncaps b).length = 1600 := by unfold compKyberEncaps; split_ifs <;> simp only [List.length_append, compKyberCt0, compKyberSs0, compKyberCt1, compKyberSs1, compKyberCt2, compKyberSs2, compDefaultKyberCt, compDefaultKyberSs, CompRBobInit.leBytes_length', List.length_replicate]
  rw [List.length_drop, hL]
theorem gamma_kemEncap_snd_length' {pk e : DY.Bytes} (he : (gamma compI0 S g e).length = 32) : (gamma compI0 S g (DY.PQKem.kemEncap pk e).2).length = 32 := by rw [CompRWSBobChain.gamma_kemEncap_snd_compI0]; simp only [he, ite_true]; exact compKyberEncaps_drop1568_length' (gamma compI0 S g e)
theorem compKyberEncaps_e0' : compKyberEncaps compKyberE0 = compKyberCt0 ++ compKyberSs0 := by unfold compKyberEncaps; simp
theorem gamma_kemEncap_fst_of_e0 {pk e : DY.Bytes} (he : gamma compI0 S g e = compKyberE0) : gamma compI0 S g (DY.PQKem.kemEncap pk e).1 = compKyberCt0 := by
  have h32 : (gamma compI0 S g e).length = 32 := by rw [he]; decide +kernel
  have h : compI0 DY.Libsignal.PQXDH.Refinement.kyberEncapsSymbol [gamma compI0 S g pk, gamma compI0 S g e] = some (compKyberEncaps (gamma compI0 S g e)) := rfl; rw [Census443Memo.gamma_kemEncap_fst_eq h32, h, Option.getD_some, he, compKyberEncaps_e0', List.take_left' Census443Memo.kyberCtVals_lengths.1]
theorem gamma_kemEncap_snd_of_e0 {pk e : DY.Bytes} (he : gamma compI0 S g e = compKyberE0) : gamma compI0 S g (DY.PQKem.kemEncap pk e).2 = compKyberSs0 := by
  have h32 : (gamma compI0 S g e).length = 32 := by rw [he]; decide +kernel
  have h : compI0 DY.Libsignal.PQXDH.Refinement.kyberEncapsSymbol [gamma compI0 S g pk, gamma compI0 S g e] = some (compKyberEncaps (gamma compI0 S g e)) := rfl; rw [Census443Memo.gamma_kemEncap_snd_eq h32, h, Option.getD_some, he, compKyberEncaps_e0', List.drop_left' Census443Memo.kyberCtVals_lengths.1]
theorem aliceOut_ck_length (tr : ExecTrace) (ikA ikBPk spkPk pqPk : DY.Bytes) (opk : Option DY.Bytes) : (gamma compI0 S g (iniAliceOut tr ikA ikBPk spkPk pqPk opk).keys.ck).length = 32 := by obtain ⟨_, hk⟩ := CompRSplit38Untagged.iniAliceOut_keys tr ikA ikBPk spkPk pqPk opk; rw [hk]; exact CompFreshDistinct.gamma_hmac_length S g _ _
theorem aliceOut_ck_not_kdfFree (tr : ExecTrace) (ikA ikBPk spkPk pqPk : DY.Bytes) (opk : Option DY.Bytes) : ¬ KdfFree (gamma compI0 S g (iniAliceOut tr ikA ikBPk spkPk pqPk opk).keys.ck) := by obtain ⟨_, hk⟩ := CompRSplit38Untagged.iniAliceOut_keys tr ikA ikBPk spkPk pqPk opk; rw [hk]; exact not_kdfFree_kdfExtract _ _
theorem gamma_agree_length (pk sk : DY.Bytes) : (gamma compI0 S g (DY.Libsignal.PQXDH.agree pk sk)).length = 32 := CompFreshDistinct.gamma_dh_length S g (DY.X25519.x25519Key pk) sk
theorem nrcensus_spqrA2B {allT rT : List DY.Bytes} : FnCensus allT rT S g DY.Libsignal.TripleRatchet.spqrA2B := nrcensus_lit_size _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem nrcensus_spqrIdx_one {allT rT : List DY.Bytes} : FnCensus allT rT S g (DY.Spqr.spqrIdx 1) :=
  nrcensus_lit_size _ (by simp [ByteArray.size]) (by simp [ByteArray.size]) (by simp [ByteArray.size]) (by simp [ByteArray.size]) (by simp [ByteArray.size]) (by decide)
theorem nrcensus_aliceOut {r : Records} (hNe : r.alice ≠ r.bob) (tr₁ tr₂ : ExecTrace) (b : DY.Participant) (o' : DY.Libsignal.PQXDH.AliceHandshakeOut) (cl : Nat) (hent : (gamma compI0 S g (randTerm (tr₁.length + 1) 32)).length = 32) : let o := iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none; FnCensus38 tr₁ tr₂ b o' cl S g o.ikA ∧ FnCensus38 tr₁ tr₂ b o' cl S g o.ikB ∧ FnCensus38 tr₁ tr₂ b o' cl S g o.spk ∧ FnCensus38 tr₁ tr₂ b o' cl S g o.ek ∧
    FnCensus38 tr₁ tr₂ b o' cl S g o.ct ∧ FnCensus38 tr₁ tr₂ b o' cl S g o.keys.rk ∧ FnCensus38 tr₁ tr₂ b o' cl S g o.keys.ck ∧ FnCensus38 tr₁ tr₂ b o' cl S g o.keys.pqr := by
  dsimp only; rw [CompSetupSecrecy.setupSecret_0 hNe, CompSetupSecrecy.setupPublic_2 hNe, CompSetupSecrecy.setupPublic_4 hNe, CompSetupSecrecy.setupPublic_6 hNe]; have hsec0 : FnCensus38 tr₁ tr₂ b o' cl S g (randTerm 0 32) := nrcensus_randTerm38 (by simp [rTerms38]); have hpub2 : FnCensus38 tr₁ tr₂ b o' cl S g (DY.DiffieHellman.dhPk (randTerm 5 32)) := nrcensus_dhPk (by simp [allTerms38]) (nrcensus_randTerm38 (by simp [rTerms38])); have hpub4 : FnCensus38 tr₁ tr₂ b o' cl S g (DY.DiffieHellman.dhPk (randTerm 10 32)) := nrcensus_dhPk (by simp [allTerms38]) (nrcensus_randTerm38 (by simp [rTerms38])); have hpub6 : FnCensus38 tr₁ tr₂ b o' cl S g (DY.PQKem.kemPk (randTerm 16 64)) := memoOK_kemPk (nrcensus_randTerm38 (by simp [rTerms38])); have hek_r : FnCensus38 tr₁ tr₂ b o' cl S g (randTerm tr₁.length 32) := nrcensus_randTerm38 (by simp [rTerms38]); have hent_r : FnCensus38 tr₁ tr₂ b o' cl S g (randTerm (tr₁.length + 1) 32) := nrcensus_randTerm38 (by simp [rTerms38])
  rcases nrcensus_pqxdhKdf_none (gamma_agree_length _ _) (gamma_agree_length _ _) (gamma_agree_length _ _) (gamma_kemEncap_snd_length' hent) (gamma_agree_mem_x25519Vals _ _)
    (nrcensus_agree_dhPk (by simp [allTerms38]) (by simp [allTerms38]) hpub4 hsec0) (nrcensus_agree_dhPk (by simp [allTerms38]) (by simp [allTerms38]) hpub2 hek_r)
    (nrcensus_agree_dhPk (by simp [allTerms38]) (by simp [allTerms38]) hpub4 hek_r)
    (memoOK_kemEncap_snd (fun _ hx => fnok_of_r ((Symbolic.Proofs.Swarm.Leaves.IC13_Stage1Kyber.assumedInjective_eq_true_iff _).mpr (by rw [Symbolic.Proofs.Swarm.Leaves.IC13_Stage1Kyber.kemEncap_snd_eq_pack]; simp [DY.BytesView.view_pack])) (by simp [allTerms38, rTerms38]) (by simp [rTerms38]) hx) hpub6 hent_r) with ⟨hrk, hck, hpqr⟩
  exact ⟨nrcensus_dhPk (by simp [allTerms38]) hsec0, hpub2, hpub4, nrcensus_dhPk (by simp [allTerms38]) hek_r,
    memoOK_kemEncap_fst (fun _ hx => fnok_of_r ((Symbolic.Proofs.Swarm.Leaves.IC13_Stage1Kyber.assumedInjective_eq_true_iff _).mpr (by rw [Symbolic.Proofs.Swarm.Leaves.IC13_Stage1Kyber.kemEncap_fst_eq_pack]; simp [DY.BytesView.view_pack])) (by simp [allTerms38, rTerms38]) (by simp [rTerms38]) hx) hpub6 hent_r, hrk, hck, hpqr⟩
theorem trStateNRC_stA {r : Records} (hNe : r.alice ≠ r.bob) (hB : r.bob = "bob") (tr₁ tr₂ : ExecTrace) (cl : Nat) (hent : (gamma compI0 S g (randTerm (tr₁.length + 1) 32)).length = 32) : let o := iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none;
    TRStateNRC (allTerms38 tr₁ tr₂ r.bob o cl) (rTerms38 tr₁ tr₂ r.bob o cl) S g (iniAliceStartState tr₁ r.bob o) := by
  intro o; obtain ⟨hikA, hikB, hspk, _, _, hrk, hck, hpqr⟩ := nrcensus_aliceOut (S := S) (g := g) hNe tr₁ tr₂ r.bob o cl hent; have hspk_eq : o.spk = DY.DiffieHellman.dhPk (randTerm 10 32) := CompSetupSecrecy.setupPublic_4 hNe
  have hikBL : (gamma compI0 S g o.ikB).length = 32 := by change (gamma compI0 S g (setupPublic r 2)).length = 32; rw [CompSetupSecrecy.setupPublic_2 hNe]; exact CompFreshDistinct.gamma_dhPk_length S g _
  have hspkL : (gamma compI0 S g o.spk).length = 32 := by rw [hspk_eq]; exact CompFreshDistinct.gamma_dhPk_length S g _
  have hrkL : (gamma compI0 S g o.keys.rk).length = 32 := CompRPreMemo38KdfCensus.aliceOut_rk_length tr₁ _ _ _ _ _; have hdhsA : FnCensus38 tr₁ tr₂ r.bob o cl S g (randTerm (tr₁.length + 2) 32) := nrcensus_randTerm38 (by simp [rTerms38])
  have hcc : FnCensus38 tr₁ tr₂ r.bob o cl S g (DY.Libsignal.TripleRatchet.createChain o.keys.rk o.spk (randTerm (tr₁.length + 2) 32)).1 ∧
      FnCensus38 tr₁ tr₂ r.bob o cl S g (DY.Libsignal.TripleRatchet.createChain o.keys.rk o.spk (randTerm (tr₁.length + 2) 32)).2 := by
    rw [hspk_eq] at hspk ⊢; exact nrcensus_createChain_dhPk (by simp [allTerms38]) (by simp [allTerms38]) hrk hspk hdhsA
  obtain ⟨hrecv, hrecvT⟩ := nrcensus_serialize_recv1 (S := S) (g := g) hspk hck (aliceOut_ck_not_kdfFree tr₁ _ _ _ _ _) (aliceOut_ck_length tr₁ _ _ _ _ _)
  exact { peer := Or.inr hB, myIk := nrcensus_serializedIk (CompFreshDistinct.gamma_dhPk_length S g _) hikA, peerIk := nrcensus_serializedIk hikBL hikB, rk := hcc.1, dhs := hdhsA, cks := hcc.2, ns_val := Or.inl rfl, pn_val := rfl, sid := nrcensus_concat (not_rv38HB_of_x25519_append (gamma_mem_x25519Vals_of_isX (Or.inl ⟨_, rfl⟩)) hrkL) (nrcensus_dhPk (by simp [allTerms38]) hdhsA) hrk, spqr := memoOK_spqrInit hpqr nrcensus_spqrA2B, recv := hrecv, recvT := hrecvT, myIkL := gamma_serializedIk_length (CompFreshDistinct.gamma_dhPk_length S g _), peerIkL := gamma_serializedIk_length hikBL }
theorem trStateNRC_encSt {tr₁ tr₂ : ExecTrace} {b : DY.Participant} {o : DY.Libsignal.PQXDH.AliceHandshakeOut} {stA : DY.Libsignal.TripleRatchet.TRState} (cl : Nat) (hns : stA.ns = 0) (hst : TRStateNRC (allTerms38 tr₁ tr₂ b o cl) (rTerms38 tr₁ tr₂ b o cl) S g stA) : TRStateNRC (allTerms38 tr₁ tr₂ b o cl) (rTerms38 tr₁ tr₂ b o cl) S g (encSt tr₂ stA cl) :=
  { hst with cks := (nrcensus_kdfCk hst.cks).1, ns_val := Or.inr (by dsimp [encSt]; rw [hns]; rfl), spqr := memoOK_spqrSendState hst.spqr (nrcensus_randTerm38 (by simp [rTerms38])) }
theorem nrcensus_enc {tr₁ tr₂ : ExecTrace} {b : DY.Participant} {o : DY.Libsignal.PQXDH.AliceHandshakeOut} {cl : Nat} (hst : TRStateNRC (allTerms38 tr₁ tr₂ b o cl) (rTerms38 tr₁ tr₂ b o cl) S g (iniAliceStartState tr₁ b o)) (hsalt : FnCensus38 tr₁ tr₂ b o cl S g (encSalt tr₂ (iniAliceStartState tr₁ b o) cl (tr₂.length + 2))) (hwL : 69 ≤ (gamma compI0 S g (encWire tr₂ (iniAliceStartState tr₁ b o) cl (tr₂.length + 2))).length) (hwU : (gamma compI0 S g (encWire tr₂ (iniAliceStartState tr₁ b o) cl (tr₂.length + 2))).length ≤ 1400) : let stA := iniAliceStartState tr₁ b o; let pq := tr₂.length + 2; let seed := (DY.Libsignal.TripleRatchet.kdfCk stA.cks).2;
    let akeys := encMsgKeys tr₂ stA cl pq; let zkeys := DY.Libsignal.TripleRatchet.trMsgKeys DY.Spqr.zeroKey seed;
    FnCensus38 tr₁ tr₂ b o cl S g (encWire tr₂ stA cl pq) ∧ FnCensus38 tr₁ tr₂ b o cl S g (encOut tr₂ stA cl pq) ∧ FnCensus38 tr₁ tr₂ b o cl S g (encMac tr₂ stA cl pq) ∧ FnCensus38 tr₁ tr₂ b o cl S g (DY.Trunc.trunc8 (zfullT tr₂ stA cl pq)) ∧ (FnCensus38 tr₁ tr₂ b o cl S g akeys.cipherKey ∧ FnCensus38 tr₁ tr₂ b o cl S g akeys.macKey ∧ FnCensus38 tr₁ tr₂ b o cl S g akeys.iv) ∧
    (FnCensus38 tr₁ tr₂ b o cl S g zkeys.cipherKey ∧ FnCensus38 tr₁ tr₂ b o cl S g zkeys.macKey ∧ FnCensus38 tr₁ tr₂ b o cl S g zkeys.iv) := by
  dsimp only; have hseed := (nrcensus_kdfCk hst.cks).2; have hmk := nrcensus_trMsgKeys hsalt hseed; have hzmk := nrcensus_trMsgKeys nrcensus_zeroKey hseed
  have hct : FnCensus38 tr₁ tr₂ b o cl S g (DY.SymEnc.symEnc (encKeys tr₂ (iniAliceStartState tr₁ b o) cl (tr₂.length + 2)).cipherKey (encKeys tr₂ (iniAliceStartState tr₁ b o) cl (tr₂.length + 2)).iv (randTerm tr₂.length 32)) :=
    nrcensus_symEnc38 (by simp [rTerms38]) hmk.1 hmk.2.2 (nrcensus_randTerm38 (by simp [rTerms38]))
  have hrk := nrcensus_dhPk (by simp [allTerms38, iniAliceStartState]) hst.dhs; have h1568 : (gamma compI0 S g (encWire tr₂ (iniAliceStartState tr₁ b o) cl (tr₂.length + 2))).length ≠ 1568 := (by omega); have hwire : FnCensus38 tr₁ tr₂ b o cl S g (encWire tr₂ (iniAliceStartState tr₁ b o) cl (tr₂.length + 2)) := (by unfold encWire DY.Libsignal.TripleRatchet.trHonestWireMsg; exact nrcensus_trWire_of_len hwL h1568 hrk hct (memoOK_spqrSendMsg hst.spqr (nrcensus_randTerm38 (by simp [rTerms38])))); have h1 := hst.myIkL; have h2 := hst.peerIkL
  have hmacIn : FnCensus38 tr₁ tr₂ b o cl S g (DY.Concat.concat (iniAliceStartState tr₁ b o).myIk (DY.Concat.concat (iniAliceStartState tr₁ b o).peerIk (encWire tr₂ (iniAliceStartState tr₁ b o) cl (tr₂.length + 2)))) :=
    nrcensus_concat (not_rv38HB_of_len_gt68 (by rw [List.length_append, gamma_concat_eq, List.length_append]; omega) (by rw [List.length_append, gamma_concat_eq, List.length_append]; omega)) hst.myIk
      (nrcensus_concat (not_rv38HB_of_len_gt68 (by rw [List.length_append]; omega) (by rw [List.length_append]; omega)) hst.peerIk hwire)
  have hmac : FnCensus38 tr₁ tr₂ b o cl S g (encMac tr₂ (iniAliceStartState tr₁ b o) cl (tr₂.length + 2)) :=
    nrcensus_trunc8 (by change encMac tr₂ (iniAliceStartState tr₁ b o) cl (tr₂.length + 2) ∈ allTerms38 tr₁ tr₂ b o cl; simp [allTerms38]) (nrcensus_hmac hmk.2.1 hmacIn)
  have hzmac : FnCensus38 tr₁ tr₂ b o cl S g (DY.Trunc.trunc8 (zfullT tr₂ (iniAliceStartState tr₁ b o) cl (tr₂.length + 2))) :=
    nrcensus_trunc8 (by simp [allTerms38, zfullT]) (nrcensus_hmac hzmk.2.1 hmacIn)
  have h3 : (gamma compI0 S g (encMac tr₂ (iniAliceStartState tr₁ b o) cl (tr₂.length + 2))).length ≤ 8 := gamma_trunc8_length_le _
  have hencOut : FnCensus38 tr₁ tr₂ b o cl S g (encOut tr₂ (iniAliceStartState tr₁ b o) cl (tr₂.length + 2)) :=
    nrcensus_concat (not_rv38HB_of_len_gt68 (by rw [List.length_append]; omega) (by rw [List.length_append]; omega)) hwire hmac
  exact ⟨hwire, hencOut, hmac, hzmac, hmk, hzmk⟩
theorem nrcensus_encSalt_stA {r : Records} (hNe : r.alice ≠ r.bob) (tr₁ tr₂ : ExecTrace) (cl : Nat) (hent : (gamma compI0 S g (randTerm (tr₁.length + 1) 32)).length = 32) : let o := iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none;
    FnCensus38 tr₁ tr₂ r.bob o cl S g (encSalt tr₂ (iniAliceStartState tr₁ r.bob o) cl (tr₂.length + 2)) := by
  intro o; obtain ⟨_, _, _, _, _, _, _, hpqr⟩ := nrcensus_aliceOut (S := S) (g := g) hNe tr₁ tr₂ r.bob o cl hent; rw [encSalt_iniAliceStartState_eq_spqrChainKey]; exact memoOK_spqrChainKey hpqr nrcensus_spqrA2B nrcensus_spqrIdx_one
theorem nrcensus_prefixTerms {allT rT : List DY.Bytes} {r : Records} {tr : ExecTrace} {vis : List VisEntry} (hsend : ∀ v ∈ vis, v.kind = .send → ∀ u ∈ v.terms, FnCensus allT rT S g u) (hstates : ∀ ls ∈ storedStates r tr, FnCensus allT rT S g (Comparse.serialize ls)) (hsecrets : ∀ u ∈ storedSecrets tr, FnCensus allT rT S g u) (hpt : ∀ v ∈ vis, v.kind = .pt → ∀ u ∈ v.terms, FnCensus allT rT S g u) : ∀ u ∈ prefixTerms r tr vis, FnCensus allT rT S g u := by
  intro u hu; unfold prefixTerms principalTerms plaintextTerms at hu; simp only [List.mem_append, List.mem_flatMap, List.mem_filter, List.mem_map, beq_iff_eq] at hu
  rcases hu with ((⟨v, ⟨hv_mem, hv_kind⟩, hu_v⟩ | ⟨ls, hls, rfl⟩) | hsec) | ⟨v, ⟨hv_mem, hv_kind⟩, hu_v⟩
  · exact hsend v hv_mem hv_kind u hu_v
  · exact hstates ls hls
  · exact hsecrets u hsec
  · exact hpt v hv_mem hv_kind u hu_v
theorem isX_ai_not_kdf {b : DY.Bytes} (h : IsX b) : assumedInjective b = true ∧ ¬ IsKdf b := by
  rcases h with ⟨x, rfl⟩ | ⟨a, c, rfl⟩
  · exact ⟨(Symbolic.Proofs.Swarm.Leaves.IC13_Stage1Kyber.assumedInjective_eq_true_iff _).mpr (by simp [show DY.DiffieHellman.dhPk x = ({ sk := x } : DY.DiffieHellman.DhPk.SubF DY.Bytes).pack from rfl, DY.BytesView.view_pack]), fun ⟨_, _, he⟩ => Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsTrue.dhPk_ne_kdfExtract _ _ _ he⟩
  · exact ⟨(Symbolic.Proofs.Swarm.Leaves.IC13_Stage1Kyber.assumedInjective_eq_true_iff _).mpr (by simp [DY.BytesView.view_pack]), fun ⟨_, _, he⟩ => Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsTrue.dh_pack_ne_kdfExtract _ _ _ _ he⟩
theorem isTrunc8_ai_not_kdf {b : DY.Bytes} (h : IsTrunc8 b) : assumedInjective b = true ∧ ¬ IsKdf b := by
  rcases h with ⟨a, rfl⟩
  exact ⟨(Symbolic.Proofs.Swarm.Leaves.IC13_Stage1Kyber.assumedInjective_eq_true_iff _).mpr (by simp [show DY.Trunc.trunc8 a = ({ input := a } : DY.Trunc.Trunc8.SubF DY.Bytes).pack from rfl, DY.BytesView.view_pack]), fun ⟨_, _, he⟩ => Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsTrue.trunc8_ne_kdfExtract _ _ _ he⟩
theorem rVals38HBOf_mem_rVals38HB {c v : HwBytes} (hv : v ∈ rVals38HBOf c) (hc : v = c → c ∈ (List.inits CompRX0SS38.cB).tail) : v ∈ rVals38HB := by
  simp only [rVals38HBOf, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact rVals38HBOf_sub_rVals38HB cB_mem_inits_tail (by simp [rVals38HBOf])
  · exact rVals38HBOf_sub_rVals38HB cB_mem_inits_tail (by simp [rVals38HBOf])
  · exact rVals38HBOf_sub_rVals38HB cB_mem_inits_tail (by simp [rVals38HBOf])
  · exact rVals38HBOf_sub_rVals38HB cB_mem_inits_tail (by simp [rVals38HBOf])
  · exact rVals38HBOf_sub_rVals38HB cB_mem_inits_tail (by simp [rVals38HBOf])
  · exact rVals38HBOf_sub_rVals38HB cB_mem_inits_tail (by simp [rVals38HBOf])
  · exact rVals38HBOf_sub_rVals38HB cB_mem_inits_tail (by simp [rVals38HBOf])
  · exact rVals38HBOf_sub_rVals38HB cB_mem_inits_tail (by simp [rVals38HBOf])
  · exact rVals38HBOf_sub_rVals38HB (hc rfl) (by simp [rVals38HBOf])
  · exact rVals38HBOf_sub_rVals38HB cB_mem_inits_tail (by simp [rVals38HBOf])
  · exact rVals38HBOf_sub_rVals38HB cB_mem_inits_tail (by simp [rVals38HBOf])
  · exact rVals38HBOf_sub_rVals38HB cB_mem_inits_tail (by simp [rVals38HBOf])
theorem assumedInjective_randTerm_zero (ts : Nat) : assumedInjective (randTerm ts 0) = false := by
  unfold randTerm
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsTrue.randTerm_zero_view? ts
  rw [Bool.eq_false_iff, ne_eq, Symbolic.Proofs.Swarm.Leaves.IC13_Stage1Kyber.assumedInjective_eq_true_iff]
  intro h; simp [h1, h2, h3, h4, h5, h6, h7, h8] at h
theorem mem_inits_tail_of_take {α : Type} :
    ∀ (xs : List α) {n : Nat}, n ≠ 0 → n ≤ xs.length → xs.take n ∈ (List.inits xs).tail
  | [], _, hn0, hle => absurd (Nat.le_zero.mp hle) hn0
  | x :: xs, n + 1, _, hle => by
    simp only [List.length_cons] at hle
    simp only [List.take_succ_cons, List.inits_cons, List.tail_cons, List.mem_map]
    exact ⟨xs.take n, CliCoinSplit.mem_inits_of_take xs (by omega), rfl⟩
theorem restFnEntry_of_fnOK {tr₁ tr₂ : ExecTrace} {b : DY.Participant} {o : DY.Libsignal.PQXDH.AliceHandshakeOut} {cl : Nat} {c : HwBytes} (hc_eq : gamma compI0 S g (randTerm (tr₂.length + 1) cl) = c) (hc : cl ≠ 0 → c ∈ (List.inits CompRX0SS38.cB).tail) (hmapR : (rTerms38 tr₁ tr₂ b o cl).map (gamma compI0 S g) = rVals38HBOf c) (hnd : ((allTerms38 tr₁ tr₂ b o cl).map (gamma compI0 S g)).Nodup) {x : DY.Bytes × DY.Bytes × HwBytes} (hv : x.2.2 = gamma compI0 S g x.1) (hok : FnOK (allTerms38 tr₁ tr₂ b o cl) (rTerms38 tr₁ tr₂ b o cl) x) : RestFnEntry (lookupShape S g (allTerms38 tr₁ tr₂ b o cl)) Rv38HB S g x := by
  refine ⟨fun h => ?_, fun hai hK hX hT => ?_, hok.1⟩
  · have ⟨hai, hK⟩ := h.elim isX_ai_not_kdf (fun h' => h'.elim isTrunc8_ai_not_kdf id); rw [hv]; exact lookupShape_eq hnd (hok.2.1 hai hK)
  · change x.2.2 ∈ rVals38HB
    have hmR := hok.2.2 hai hK hX hT
    have hv_mem : x.2.2 ∈ rVals38HBOf c := by rw [hv, ← hmapR]; exact List.mem_map_of_mem hmR
    refine rVals38HBOf_mem_rVals38HB hv_mem (fun hvc => hc (fun hcl => ?_))
    have hx_eq : x.1 = randTerm (tr₂.length + 1) cl :=
      List.inj_on_of_nodup_map hnd (List.mem_append_left _ hmR) (by simp [allTerms38, rTerms38]) (hv.symm.trans (hvc.trans hc_eq.symm))
    rw [hx_eq, hcl, assumedInjective_randTerm_zero] at hai; cases hai
theorem encrypt_next_wrap_eq (me : DY.Participant) (s cl pq : Nat) (w₁ w₂ : Option (Nat × Nat)) (tr : ExecTrace) : (Move.encrypt me s cl pq w₁).next tr = (Move.encrypt me s cl pq w₂).next tr := rfl
theorem gamma_randTerm_16 {r : Records} (hNe : r.alice ≠ r.bob) (hc : Compat compI0 r S g) : gamma compI0 S g (randTerm 16 64) = secretBytes r 4 := by
  rw [CompRX0Bytes.gamma_randTerm']; simp only [show (64 : Nat) ≠ 0 by decide, ↓reduceIte]; rw [hc.1 (16, 64) (CompPrefixInvFresh.mem_setupRandomsAt_64 r hNe (List.mem_cons_of_mem 11 List.mem_cons_self))]
  unfold secretBytes; rw [Symbolic.Swarm.CREF.b1_setupRandomsAt_eq r hNe]; cases r.withOpk <;> rfl
theorem gamma_agree_dhPk_of_eq {t₁ t₂ : DY.Bytes} {b₁ b₂ : HwBytes} (h₁ : gamma compI0 S g t₁ = b₁) (h₂ : gamma compI0 S g t₂ = b₂) (heq : compLookupDh (clamp b₁) (compLookupPub (clamp b₂)) = compLookupDh (clamp b₂) (compLookupPub (clamp b₁))) : gamma compI0 S g (DY.Libsignal.PQXDH.agree (DY.DiffieHellman.dhPk t₁) t₂) = compLookupDh (clamp b₂) (compLookupPub (clamp b₁)) := by
  have hv : (DY.DiffieHellman.dhPk t₁).view? DY.DiffieHellman.DhPk.SubF = some { sk := t₁ } := by dsimp only [DY.DiffieHellman.dhPk, DY.DiffieHellman.CanDH.dhPk]; rw [DY.BytesView.view_pack]
  simp only [DY.Libsignal.PQXDH.agree, CompPlant.x25519Key_dhPk, DY.DiffieHellman.dh, DY.DiffieHellman.CanDH.dh, hv]
  split_ifs
  · rw [CompFreshDistinct.gamma_dh_pack_compI0, show ({ sk := t₁ } : DY.DiffieHellman.DhPk.SubF DY.Bytes).pack = DY.DiffieHellman.dhPk t₁ from rfl, CompFreshDistinct.gamma_dhPk_compI0, h₁, h₂]
  · rw [CompFreshDistinct.gamma_dh_pack_compI0, show ({ sk := t₂ } : DY.DiffieHellman.DhPk.SubF DY.Bytes).pack = DY.DiffieHellman.dhPk t₂ from rfl, CompFreshDistinct.gamma_dhPk_compI0, h₁, h₂, heq]
theorem hb_dh_comm : compLookupDh (clamp Witnesses.Cheval26SmallSubgroupHighBitComp.setup.spk) (compLookupPub (clamp Witnesses.Cheval26SmallSubgroupHighBitComp.setup.aliceId)) = compLookupDh (clamp Witnesses.Cheval26SmallSubgroupHighBitComp.setup.aliceId) (compLookupPub (clamp Witnesses.Cheval26SmallSubgroupHighBitComp.setup.spk)) ∧ compLookupDh (clamp Witnesses.Cheval26SmallSubgroupHighBitComp.setup.bobId) (compLookupPub (clamp CompRX0SS38.b0Bytes)) = compLookupDh (clamp CompRX0SS38.b0Bytes) (compLookupPub (clamp Witnesses.Cheval26SmallSubgroupHighBitComp.setup.bobId)) ∧ compLookupDh (clamp Witnesses.Cheval26SmallSubgroupHighBitComp.setup.spk) (compLookupPub (clamp CompRX0SS38.b0Bytes)) = compLookupDh (clamp CompRX0SS38.b0Bytes) (compLookupPub (clamp Witnesses.Cheval26SmallSubgroupHighBitComp.setup.spk)) ∧ compLookupDh (clamp Witnesses.Cheval26SmallSubgroupHighBitComp.setup.spk) (compLookupPub (clamp ssDhsBytes)) = compLookupDh (clamp ssDhsBytes) (compLookupPub (clamp Witnesses.Cheval26SmallSubgroupHighBitComp.setup.spk)) := by decide +kernel
attribute [local irreducible] Symbolic.BugInjection.hexBytes setupSecret setupPublic setupTrace
theorem rest38Fn_of_wirePairOk_split {w : PQXDHSpqrSetup} {blk₁ : List MachineEvent} {wire : HwBytes} {v : Fin 4} {t : Fin 8} (haliceId : w.aliceId = Witnesses.Cheval26SmallSubgroupHighBitComp.setup.aliceId) (hbobId : w.bobId = Witnesses.Cheval26SmallSubgroupHighBitComp.setup.bobId) (hspk : w.spk = Witnesses.Cheval26SmallSubgroupHighBitComp.setup.spk) (hcs : DY.Libsignal.Composed.Refinement.Cli.CoinSplit [.pt CompRX0SS38.ptB, .rng CompRX0SS38.cB, .send CompRPlantWire.sentWireBytes] blk₁) : Rest38FnAt w ([.recv bunBytes, .rng CompRX0SS38.b0Bytes] ++ CompRX0SS38.rsT ++ blk₁) wire v t := by
  intro r S g p hfitsP _hp hopk pre mid post hb shown cl e c'; have hfits : compFits w compI0 r := CompFitsNames.compFits_base hfitsP; dsimp only; intro hc hmr hvis hpre hmid hpost hm₀ _hbd; let tr₁ := (runMoves pre (setupTrace r)).1; let o := iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none; let m₀ := Move.aliceStart r.alice r.bob 4 6 hb shown; let tr₂ := (runMoves mid (m₀.next tr₁)).1; let pq := tr₂.length + 2; let stA := iniAliceStartState tr₁ r.bob o; let ms := pre ++ m₀ :: mid ++ Move.encrypt r.alice (tr₁.length + 8) cl pq (some (e, c')) :: post; let ms' := pre ++ m₀ :: mid ++ Move.encrypt r.alice (tr₁.length + 8) cl pq (some (tr₁.length + 3, tr₁.length + 4)) :: post; let x₀ : PreKeyRep := ⟨DY.X25519.x25519TorsionVariant o.ek v t, o.ct, encOut tr₂ stA cl pq⟩; have hNe : r.alice ≠ r.bob := hfits.1.1; have hA : r.alice = "alice" := CompFitsNames.compFits_alice hfitsP; have hB : r.bob = "bob" := CompFitsNames.compFits_bob hfitsP; obtain ⟨hvis₀, hm₁⟩ := CompC3RestPre38HB.split38_forall2_vis_inv_split hNe rfl hpre hmid hpost hm₀ CompRX0SS38.rsT_len CompC3RestPre38HB.rsT_kind' hvis; obtain ⟨hb0_s, hcoins, hdhs_s⟩ := aliceVis_dhs_coin CompRX0SS38.rsT_len rsT_drop32 hvis₀; obtain ⟨q₀, hq₀, _⟩ := sentWireBytes_innerWireCanonical.1; obtain ⟨hpt_s, hc_in, hmsg⟩ := CompC3RestPre38HB.encVis_split38_pins_split hcs CompRX0SS38.sentWireBytes_len hq₀ hm₁; obtain ⟨_, ⟨n, hn_le, hcl_iff, hc_eq, _⟩, _⟩ := CliCoinSplit.encVis_of_coinSplit_send hcs hm₁; have hc_eq' : gamma compI0 S g (randTerm (tr₂.length + 1) cl) = CompRX0SS38.cB.take n := hc_eq; have h0 : gamma compI0 S g (randTerm 0 32) = Witnesses.Cheval26SmallSubgroupHighBitComp.setup.aliceId := (by rw [← CompSetupSecrecy.setupSecret_0 hNe, CompRWSBobChain.gamma_setupSecret_0 hNe hc, hfits.2.2.2.2.2.2.1, haliceId]); have h5 : gamma compI0 S g (randTerm 5 32) = Witnesses.Cheval26SmallSubgroupHighBitComp.setup.bobId := (by rw [← CompSetupSecrecy.setupSecret_1 hNe, CompRX0Bytes.gamma_setupSecret_1 hNe hc, hfits.2.2.2.2.2.2.2.1, hbobId]); have h10 : gamma compI0 S g (randTerm 10 32) = Witnesses.Cheval26SmallSubgroupHighBitComp.setup.spk := (by rw [← CompSetupSecrecy.setupSecret_2 hNe, CompRX0Bytes.gamma_setupSecret_2 hNe hc, hfits.2.2.2.2.2.2.2.2.1, hspk]); have h16 : gamma compI0 S g (randTerm 16 64) = fillFresh 16 64 := (gamma_randTerm_16 hNe hc).trans (CompFitsNames.compFits_secretBytes_fresh hfitsP).2.1; have hb0 : gamma compI0 S g (randTerm tr₁.length 32) = CompRX0SS38.b0Bytes := single_eq_inv hb0_s; have he0 : gamma compI0 S g (randTerm (tr₁.length + 1) 32) = compKyberE0 := (CompRX0Gamma.gamma_of_kyberCoins hcoins).trans CompRX0SS38.rsT_coinHeads_eq; have hdhs : gamma compI0 S g (randTerm (tr₁.length + 2) 32) = ssDhsBytes := single_eq_inv hdhs_s; have hpt : gamma compI0 S g (randTerm tr₂.length 32) = CompRX0SS38.ptB := single_eq_inv hpt_s; have hc_tail : cl ≠ 0 → CompRX0SS38.cB.take n ∈ (List.inits CompRX0SS38.cB).tail := fun hcl => mem_inits_tail_of_take CompRX0SS38.cB (fun hn0 => hcl (hcl_iff.mpr hn0)) hn_le; obtain ⟨hk, hP, _, _, _, _⟩ := CompC3RestPre38HB.split38_encMac_chain_split (r := r) (S := S) (g := g) hNe hpre hmid hpost hm₀ CompRX0SS38.rsT_len CompC3RestPre38HB.rsT_kind' CompRX0SS38.sentWireBytes_len wireMacChainOk_sentWire hcs hvis; have hct : gamma compI0 S g (DY.SymEnc.symEnc (encKeys tr₂ (iniAliceStartState tr₁ r.bob o) cl (tr₂.length + 2)).cipherKey (encKeys tr₂ (iniAliceStartState tr₁ r.bob o) cl (tr₂.length + 2)).iv (randTerm tr₂.length 32)) = compAesCt0 := gamma_symEnc_encKeys_hb hk hP hpt; have hmac_val : gamma compI0 S g (encMac tr₂ (iniAliceStartState tr₁ r.bob o) cl (tr₂.length + 2)) = sentMac8 := (gamma_encWire_mac_of_encOut hmsg).2.trans (sentWireBytes_msgMac8 hq₀); have hzmac_val : gamma compI0 S g (DY.Trunc.trunc8 (zfullT tr₂ (iniAliceStartState tr₁ r.bob o) cl (tr₂.length + 2))) = CompC3Nbsc38HB.zfull0SS.take 8 := (by rw [CompFreshDistinct.gamma_trunc8_eq, (CompC3Nbsc38HB.split38_zpins_ss_split hNe hpre hmid hpost hm₀ hcs hvis).2]); have hag1 := gamma_agree_dhPk_of_eq h10 h0 hb_dh_comm.1; have hag2 := gamma_agree_dhPk_of_eq h5 hb0 hb_dh_comm.2.1; have hag3 := gamma_agree_dhPk_of_eq h10 hb0 hb_dh_comm.2.2.1; have hag4 := gamma_agree_dhPk_of_eq h10 hdhs hb_dh_comm.2.2.2; have hkct : gamma compI0 S g (DY.PQKem.kemEncap (DY.PQKem.kemPk (randTerm 16 64)) (randTerm (tr₁.length + 1) 32)).1 = compKyberCt0 := gamma_kemEncap_fst_of_e0 he0; have hkss : gamma compI0 S g (DY.PQKem.kemEncap (DY.PQKem.kemPk (randTerm 16 64)) (randTerm (tr₁.length + 1) 32)).2 = compKyberSs0 := gamma_kemEncap_snd_of_e0 he0; have hmapR : (rTerms38 tr₁ tr₂ r.bob o cl).map (gamma compI0 S g) = rVals38HBOf (CompRX0SS38.cB.take n) := (by simp only [rTerms38, rVals38HBOf, List.map_cons, List.map_nil, h0, h5, h10, h16, hb0, he0, hdhs, hpt, hc_eq', hct, hkct, hkss]); have hmapA : (allTerms38 tr₁ tr₂ r.bob o cl).map (gamma compI0 S g) = allVals38HBOf (CompRX0SS38.cB.take n) := (by simp only [allTerms38, allVals38HBOf, List.map_append, hmapR, List.map_cons, List.map_nil, CompFreshDistinct.gamma_dhPk_compI0, h0, h5, h10, hb0, hdhs, hag1, hag2, hag3, hag4, hmac_val, hzmac_val]); have hnd : ((allTerms38 tr₁ tr₂ r.bob o cl).map (gamma compI0 S g)).Nodup := hmapA ▸ allVals38HBOf_nodup (hc_eq ▸ hc_in)
  have hentL : (gamma compI0 S g (randTerm (tr₁.length + 1) 32)).length = 32 := by rw [he0]; decide +kernel
  have hwL : 69 ≤ (gamma compI0 S g (encWire tr₂ stA cl pq)).length := by have h1 := (gamma_encWire_mac_of_encOut hmsg).1; have h2 := sentWireBytes_msg_ge77 hq₀; rw [h1, List.length_take]; omega
  have hwU : (gamma compI0 S g (encWire tr₂ stA cl pq)).length ≤ 1400 := by have h1 := (gamma_encWire_mac_of_encOut hmsg).1; have h2 := sentWireBytes_msg_le1400 hq₀; rw [h1, List.length_take]; omega
  have hstA := trStateNRC_stA (S := S) (g := g) hNe hB tr₁ tr₂ cl hentL; have ho_out := nrcensus_aliceOut (S := S) (g := g) hNe tr₁ tr₂ r.bob o cl hentL; have henc := nrcensus_enc hstA (nrcensus_encSalt_stA hNe tr₁ tr₂ cl hentL) hwL hwU; have htr_eq : runTraceMoves r ms = runTraceMoves r ms' := runTrace_split38_swap_eq r pre mid post m₀ r.alice (tr₁.length + 8) cl pq (some (e, c')) (some (tr₁.length + 3, tr₁.length + 4)); have hpost' : MovesFrom InvisibleNoEffect ((Move.encrypt r.alice (tr₁.length + 8) cl pq (some (tr₁.length + 3, tr₁.length + 4))).next tr₂) post := (by rwa [encrypt_next_wrap_eq r.alice (tr₁.length + 8) cl pq (some (e, c')) (some (tr₁.length + 3, tr₁.length + 4)) tr₂] at hpost); have hpt_r : FnCensus38 tr₁ tr₂ r.bob o cl S g (randTerm tr₂.length 32) := nrcensus_randTerm38 (by simp only [rTerms38, List.mem_cons, true_or, or_true])
  have hpreTerms : ∀ u ∈ prefixTerms r (runTraceMoves r ms') (runVis r ms'), FnCensus38 tr₁ tr₂ r.bob o cl S g u := by
    refine nrcensus_prefixTerms (fun v hv hkind u hu_v => ?_) (fun ls hls => ?_) (htr_eq ▸ nrcensus_storedSecrets_hb hfitsP hc hmr.2.1 hmr.2.2.1.1) (fun v hv hkind u hu_v => ?_)
    · rcases send_terms_split38_mem hNe rfl hpre hmid hpost' hm₀ hv hkind hu_v with rfl | rfl | rfl <;> [exact ho_out.2.2.2.1; exact ho_out.2.2.2.2.1; exact henc.2.1]
    · rcases storedStates_split38_cases rfl hpre hmid hpost' hm₀ hls with hls_eq | hls_eq <;> rw [hls_eq] <;> [exact nrcensus_serialize_local_tr (Or.inl hA) hstA; exact nrcensus_serialize_local_tr (Or.inl hA) (trStateNRC_encSt cl rfl hstA)]
    · rw [pt_terms_split38_mem hNe rfl hpre hmid hpost' hm₀ hv hkind hu_v]; exact hpt_r
  have hek_key : DY.X25519.x25519Key x₀.ek = o.ek := x25519Key_torsionVariant_aliceOut_ek tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none v t
  have ho_ek : DY.X25519.x25519Key o.ek = o.ek := CompPlant.x25519Key_dhPk (randTerm tr₁.length 32)
  have hek_val : gamma compI0 S g (DY.X25519.x25519Key o.ek) = hbEkAPub := by rw [ho_ek]; change gamma compI0 S g (DY.DiffieHellman.dhPk (randTerm tr₁.length 32)) = hbEkAPub; rw [CompFreshDistinct.gamma_dhPk_compI0, hb0]; rfl
  have hnewTerms : ∀ u ∈ [x₀.ek, x₀.ct, x₀.msg] ++ bobTerms r (honestSalts r ms') p x₀, FnCensus38 tr₁ tr₂ r.bob o cl S g u := by
    have henc_step := encrypt_next_split38_eq (cl := cl) (some (tr₁.length + 3, tr₁.length + 4)) hm₀ hmid rfl; have hsalts := honestSalts_split_eq rfl rfl hpre hmid hpost' henc_step; intro u hu; simp only [List.cons_append, List.nil_append, List.mem_cons] at hu
    rcases hu with rfl | rfl | rfl | hu_bob
    · exact nrcensus_variant_ek v t hek_val (ho_ek.symm ▸ ho_out.2.2.2.1)
    · exact ho_out.2.2.2.2.1
    · exact henc.2.1
    · rw [hsalts] at hu_bob; have hu_cases := mem_bobTerms_x0_iff (tr₁ := tr₁) (tr₂ := tr₂) (cl := cl) hNe hopk hek_key rfl rfl u hu_bob; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu_cases
      rcases hu_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ho_out.2.2.2.2.2.1
      · exact ho_out.2.2.2.2.2.2.1
      · exact ho_out.2.2.2.2.2.2.2
      · exact hstA.cks
      · exact (trStateNRC_encSt cl rfl hstA).cks
      · exact henc.2.2.2.2.1.1
      · exact henc.2.2.2.2.1.2.1
      · exact henc.2.2.2.2.1.2.2
      · exact henc.2.2.1
      · exact hpt_r
      · exact henc.2.2.2.2.2.1
      · exact henc.2.2.2.2.2.2.1
      · exact henc.2.2.2.2.2.2.2
      · exact henc.2.2.2.1
  refine ⟨lookupShape S g (allTerms38 tr₁ tr₂ r.bob o cl), Rv38HB, fun x hx _hc => ?_⟩
  rcases List.mem_append.mp hx with hx_pre | hx_new
  · obtain ⟨u, hu, hxu⟩ := List.mem_flatMap.mp hx_pre; exact restFnEntry_of_fnOK hc_eq' hc_tail hmapR hnd (CompRPreMemoSound.memo_sound compI0 S g u hxu).2 (hpreTerms u hu x hxu)
  · obtain ⟨u, hu, hxu⟩ := List.mem_flatMap.mp hx_new; exact restFnEntry_of_fnOK hc_eq' hc_tail hmapR hnd (CompRPreMemoSound.memo_sound compI0 S g u hxu).2 (hnewTerms u hu x hxu)
theorem coinSplit_send_self : DY.Libsignal.Composed.Refinement.Cli.CoinSplit [.pt CompRX0SS38.ptB, .rng CompRX0SS38.cB, .send CompRPlantWire.sentWireBytes] [.pt CompRX0SS38.ptB, .rng CompRX0SS38.cB, .send CompRPlantWire.sentWireBytes] :=
  .keep (by intro _ h; cases h) (by simpa using DY.Libsignal.Composed.Refinement.Cli.CoinSplit.split (pieces := [CompRX0SS38.cB]) (by intro p hp; rcases List.mem_singleton.mp hp with rfl; decide +kernel) (by simp) (.keep (by intro _ h; cases h) .nil))
theorem rest38Fn_of_wirePairOk {w : PQXDHSpqrSetup} {τ : List MachineEvent} {wire : HwBytes} {v : Fin 4} {t : Fin 8} (haliceId : w.aliceId = Witnesses.Cheval26SmallSubgroupHighBitComp.setup.aliceId) (hbobId : w.bobId = Witnesses.Cheval26SmallSubgroupHighBitComp.setup.bobId) (hspk : w.spk = Witnesses.Cheval26SmallSubgroupHighBitComp.setup.spk) (htake : τ = [.recv bunBytes, .rng CompRX0SS38.b0Bytes] ++ CompRX0SS38.rsT ++ [.pt CompRX0SS38.ptB, .rng CompRX0SS38.cB, .send CompRPlantWire.sentWireBytes]) : Rest38FnAt w τ wire v t :=
  htake ▸ rest38Fn_of_wirePairOk_split haliceId hbobId hspk coinSplit_send_self
theorem rest38FnHB : Rest38FnHB := rest38Fn_of_wirePairOk rfl rfl rfl highBitComp_take38
theorem rest38FnTC : Rest38FnTC := rest38Fn_of_wirePairOk rfl rfl rfl torsionComp_take38
end NRSt
end Symbolic.BugInjection.Proofs.Common443.CompC3RestFn38HB
