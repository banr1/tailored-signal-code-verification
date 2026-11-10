/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Decomp81CoreAux
public import Symbolic.BugInjection.Proofs.Common443.CompPrefixInvFresh
public import Symbolic.BugInjection.Proofs.Common443.CompSetupSecrecy
public import Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.BobDone
public import Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.NoFull
public import Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtPrefixInv78a
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Decomp40
public import Symbolic.Proofs.Swarm.CREF.ModelBridge

@[expose] public section
set_option autoImplicit false
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Common443.WsIdx1Decomp81Core
open DY DY.Libsignal.Composed DY.Libsignal.Composed.Refinement DY.Libsignal.HwEvents Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompTrace Symbolic.BugInjection.Proofs.Common443.CompSetupSecrecy Symbolic.BugInjection.Proofs.Common443.CompPrefixInvStruct Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice Symbolic.BugInjection.Proofs.Common443.CompPrefixInvEnc Symbolic.BugInjection.Proofs.Common443.CompPrefixInvBundle Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Proofs.Common443
open DY.Libsignal (HwBytes) open CryptoProofLib.Refinement (ExternInterpretation)
export Symbolic.BugInjection.Proofs.Common443.WsIdx1Decomp40 (sendMatches_of_encVis2 trStateStoredAt_encNextTr' at?_trSt_encNextTr' runMoves_cons_fst₀ aliceStartState_ns_zero aliceStartState_pn_zero a_tr_eq)
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.TraceFacts in
export Symbolic.BugInjection.Proofs.Common443.WsIdx1Decomp40 (call2_pin decomp40_full)
set_option maxRecDepth 200000 in
export Symbolic.BugInjection.Proofs.Common443.WsIdx1Decomp40 (idx1_bobId_secretIdx idx1_spk_secretIdx)
export Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtPrefixInv78a (bobOutOf bobStartPreSkipTr bobFinalSt bobStartSkipTr bobStartTr bobStart_next_eq at?_pqSt_bobStartTr at?_trSt_bobStartTr at?_rnd_bobStartTr length_lt_bobStartTr gamma_rng_of_bobVis_forall2 bundle_pin_of_reachable)
theorem bobFinalSt_ns_eq {tr : ExecTrace} {a b : Participant} {kh : DY.Libsignal.PQXDH.BobKeyHandles} {regA : Nat} {mh : DY.Libsignal.PQXDH.PreKeyMsgHandles} {pqIdx : Nat} {spqrMsgIdx : UInt32} (w : BobStartOk tr b a kh regA mh pqIdx spqrMsgIdx) : (bobFinalSt tr a w).ns = 0 := rfl
theorem bobFinalSt_pn_eq {tr : ExecTrace} {a b : Participant} {kh : DY.Libsignal.PQXDH.BobKeyHandles} {regA : Nat} {mh : DY.Libsignal.PQXDH.PreKeyMsgHandles} {pqIdx : Nat} {spqrMsgIdx : UInt32} (w : BobStartOk tr b a kh regA mh pqIdx spqrMsgIdx) : (bobFinalSt tr a w).pn = 0 := rfl
theorem bobFinalSt_dhs_eq {tr : ExecTrace} {a b : Participant} {kh : DY.Libsignal.PQXDH.BobKeyHandles} {regA : Nat} {mh : DY.Libsignal.PQXDH.PreKeyMsgHandles} {pqIdx : Nat} {spqrMsgIdx : UInt32} (w : BobStartOk tr b a kh regA mh pqIdx spqrMsgIdx) : (bobFinalSt tr a w).dhs = randTerm tr.length 32 := rfl
theorem encSt_ns_eq (tr : ExecTrace) (st : DY.Libsignal.TripleRatchet.TRState) (cl : Nat) : (encSt tr st cl).ns = st.ns + 1 := rfl
theorem encSt_pn_eq (tr : ExecTrace) (st : DY.Libsignal.TripleRatchet.TRState) (cl : Nat) : (encSt tr st cl).pn = st.pn := rfl
attribute [local irreducible] DY.Libsignal.Composed.reachability in
theorem pia_bundle_inv_of_reachable
    {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost}
    {ms_pre : List Move} {tr : ExecTrace} {a b : Participant} {idS regB : Nat}
    {hb : DY.Libsignal.PQXDH.BundleHandles} {shown : Nat} {bun : HwBytes} {rs : List MachineEvent}
    (hNe : r.alice ≠ r.bob) (htr : tr = runTraceMoves r ms_pre) (hns : ∀ m ∈ ms_pre, m.isSetup = false)
    (hreach : (runTraceMoves r ms_pre).Reachable DY.Libsignal.Composed.reachability)
    (hnoleak : ∀ v ∈ runVis r ms_pre, v.kind ≠ .leak)
    (hnb : CompSetupSecrecy.NoBrk r ms_pre)
    (hpqSt : ∀ j : Nat, (tr.at? j : Option PQXDHStEntry) = ((setupTrace r).at? j : Option PQXDHStEntry))
    (hdone : (eventIdx isAliceDone tr ((Move.aliceStart a b idS regB hb shown).next tr)).isSome = true)
    (hm_vis : List.Forall₂ (EventMatchesEntry i r S g) (.recv bun :: rs)
      (aliceVis tr ((Move.aliceStart a b idS regB hb shown).next tr) hb))
    (hbun4 : bun[4]? ≠ some 1#8) :
    let m := Move.aliceStart a b idS regB hb shown
    regB = 6 ∧ b = r.bob ∧ hb.opk = none ∧ bun[4]? = some 0#8 ∧
    ∃ (ikA : DY.Bytes), ((idS = 4 ∧ a = r.alice ∧ ikA = setupSecret r 0) ∨ (idS = 9 ∧ a = r.bob ∧ ikA = setupSecret r 1)) ∧
      m.next tr = CompPrefixInvAlice.iniAliceStartTr tr a r.bob
        (CompPrefixInvAlice.iniAliceOut tr ikA (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none) := by
  obtain ⟨ikA, ikB, vkB, spk, spkSig, pqpk, pqpkSig, opk, honest,
    hstA, hregB, hspk, hspkSig, hpq, hpqSig, hv1, hv2, hopk, _, _, hnext⟩ :=
    CompPrefixInvAlice.aliceStart_inv_of_isAliceDone hdone
  obtain ⟨hhb_opk, hopk_eq, _, hbun0⟩ := CompPrefixInvAlice.hb_opk_eq_none_of_bun_byte4 hspk hspkSig hpq hpqSig hopk hm_vis hbun4
  obtain ⟨hregB_eq, hb_eq, hikB_eq, _, _, hspk_eq, hpq_eq⟩ := bundle_pin_of_reachable hNe hns hreach hnoleak hnb (htr ▸ hregB) (htr ▸ hspkSig) (htr ▸ hpqSig) hv1 hv2
  subst hb_eq; rw [hikB_eq, hspk_eq, hpq_eq, hopk_eq] at hnext
  have hstA_setup : PQXDHStoredAt (setupTrace r) a { kind := .identity, sk := ikA } idS := by
    unfold PQXDHStoredAt at hstA ⊢; rw [← hpqSt idS]; exact hstA
  exact ⟨hregB_eq, rfl, hhb_opk, hbun0, ikA, CompPrefixInvBundle.setupTrace_pqxdhStoredAt_identity hNe hstA_setup, hnext⟩
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.TraceFacts in
theorem take40_split_not_knownBaseKey {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost}
    {ms : List Move} {p : PreKeyFields} {b1 b2 : List MachineEvent}
    (hc1 : DY.Libsignal.Composed.Refinement.Cli.CoinSplit [.pt (ptAt 35), .rng (rngAt 36), .send (sendAt 37)] b1)
    (hc2 : DY.Libsignal.Composed.Refinement.Cli.CoinSplit WsIdx1CensusDefs.seg38SplitSrc b2)
    (hmp : Symbolic.Swarm.CREF.MatchedPrefix i r S g ms ((seg 0 35 ++ b1) ++ b2)) :
    ¬ KnownBaseKey i r S g ms p := by
  obtain ⟨pieces, _, _, rfl⟩ := CliCoinSplit.coinSplit_send_exit0_inv hc1
  obtain ⟨pieces₂, _, _, rfl⟩ := CliCoinSplit.coinSplit_send_exit0_inv hc2
  have htail : ∀ e ∈ pieces.map MachineEvent.rng ++ [MachineEvent.send (sendAt 37)],
      eventKind e = .rng ∨ eventKind e = .send := by
    intro e he; simp only [List.mem_append, List.mem_map, List.mem_singleton] at he
    rcases he with ⟨_, _, rfl⟩ | rfl <;> simp [eventKind]
  have htail₂ : ∀ e ∈ pieces₂.map MachineEvent.rng ++ [MachineEvent.send (WsIdx1CensusDefs.sendAt 39)],
      eventKind e = .rng ∨ eventKind e = .send := by
    intro e he; simp only [List.mem_append, List.mem_map, List.mem_singleton] at he
    rcases he with ⟨_, _, rfl⟩ | rfl <;> simp [eventKind]
  have h38 : ∀ ms₃₈, Symbolic.Swarm.CREF.MatchedPrefix i r S g ms₃₈
      (seg 0 35 ++ (.pt (ptAt 35) :: (pieces.map MachineEvent.rng ++ [.send (sendAt 37)]))) →
      AllBobDone (fun _ => False) (runTraceMoves r ms₃₈) :=
    fun ms₃₈ hmp₃₈ => Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.BobDone.allBobDone_matchedPrefix_send_tail
      htail (fun ms₃₅ h35 => Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.BobDone.take35_allBobDone
        (by rw [take35_eq, List.nil_append]; exact h35)) hmp₃₈
  exact not_knownBaseKey_of_allBobDone_false
    (Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.BobDone.allBobDone_matchedPrefix_send_tail
      htail₂ h38 hmp)
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.TraceFacts in
theorem decomp43_step {r : Records} {S : Sem} {g : Ghost} {ms₄₃ : List Move} {b1 b2 : List MachineEvent}
    (hc1 : DY.Libsignal.Composed.Refinement.Cli.CoinSplit [.pt (ptAt 35), .rng (rngAt 36), .send (sendAt 37)] b1)
    (hc2 : DY.Libsignal.Composed.Refinement.Cli.CoinSplit WsIdx1CensusDefs.seg38SplitSrc b2)
    (hmp₄₃ : Symbolic.Swarm.CREF.MatchedPrefix compI0 r S g ms₄₃ (((seg 0 35 ++ b1) ++ b2) ++ seg 40 3)) :
    ∃ (ms₄₀ pre₃ post₃ : List Move) (b_bob a_bob : Participant) (kh : DY.Libsignal.PQXDH.BobKeyHandles) (regIdxA : Nat) (mh : DY.Libsignal.PQXDH.PreKeyMsgHandles) (pqIdx : Nat) (spqrMsgIdx : UInt32) (sh_bob : Nat) (tr_bob : ExecTrace) (w_bob : BobStartOk tr_bob b_bob a_bob kh regIdxA mh pqIdx spqrMsgIdx), ms₄₃ = ms₄₀ ++ pre₃ ++ Move.bobStart b_bob a_bob kh regIdxA mh pqIdx spqrMsgIdx sh_bob :: post₃ ∧ Symbolic.Swarm.CREF.MatchedPrefix compI0 r S g ms₄₀ ((seg 0 35 ++ b1) ++ b2) ∧ tr_bob = (runMoves pre₃ (runTraceMoves r ms₄₀)).1 ∧ MovesFrom InvisibleNoEffect (runTraceMoves r ms₄₀) pre₃ ∧ MovesFrom InvisibleNoEffect ((Move.bobStart b_bob a_bob kh regIdxA mh pqIdx spqrMsgIdx sh_bob).next tr_bob) post₃ ∧ (Move.bobStart b_bob a_bob kh regIdxA mh pqIdx spqrMsgIdx sh_bob).next tr_bob = bobStartTr tr_bob b_bob a_bob w_bob ∧ gamma compI0 S g (randTerm tr_bob.length 32) = rngAt 41 := by
  have hmp' : Symbolic.Swarm.CREF.MatchedPrefix compI0 r S g ms₄₃ (((seg 0 35 ++ b1) ++ b2) ++ [.recv (wireAt 40), .rng (rngAt 41), .accept (acceptAt 42)]) := by
    rwa [← seg40_shape]
  obtain ⟨p40, hp40⟩ := wireAt40_parses
  obtain ⟨ms₄₀, pre₃, post₃, b_bob, a_bob, kh, regIdxA, mh, pqIdx, spqrMsgIdx, sh_bob,
    hms₄₃, hmp₄₀, _, hpre₃, hpost₃, _, hm_bob⟩ :=
    Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.BobDone.matchedPrefix_rpk_bobStart_only compI0 r S g _ (wireAt 40) (rngAt 41) (acceptAt 42) ms₄₃ p40 wireAt40_head? hp40
      (fun _ hmp₀ => take40_split_not_knownBaseKey hc1 hc2 hmp₀) hmp'
  let tr_bob := (runMoves pre₃ (runTraceMoves r ms₄₀)).1
  obtain ⟨w_bob, -, -⟩ := Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.NoFull.bobStartOk_of_rpk_forall2 hp40 hm_bob; have hnext_bob := bobStart_next_eq (sh := sh_bob) w_bob
  have hex : exposures tr_bob ((Move.bobStart b_bob a_bob kh regIdxA mh pqIdx spqrMsgIdx sh_bob).next tr_bob) = [] :=
    exposures_nil_of_not_leakKind rfl (fun h => nomatch h)
  have hvis_bob : (Move.bobStart b_bob a_bob kh regIdxA mh pqIdx spqrMsgIdx sh_bob).vis tr_bob =
      (bobVis tr_bob ((Move.bobStart b_bob a_bob kh regIdxA mh pqIdx spqrMsgIdx sh_bob).next tr_bob)
        mh (bobOpkPk b_bob kh tr_bob)).take sh_bob := by rw [xpl_vis_eq, hex, List.append_nil]; rfl
  have hm_bob' : List.Forall₂ (EventMatchesEntry compI0 r S g) [.recv (wireAt 40), .rng (rngAt 41), .accept (acceptAt 42)]
      ((bobVis tr_bob ((Move.bobStart b_bob a_bob kh regIdxA mh pqIdx spqrMsgIdx sh_bob).next tr_bob)
        mh (bobOpkPk b_bob kh tr_bob)).take sh_bob) := by rw [← hvis_bob]; exact hm_bob
  have hsh3 : 3 ≤ sh_bob := by have hlen := (xpl_forall₂_length hm_bob').symm; rw [List.length_take] at hlen; simp only [List.length_cons, List.length_nil] at hlen; omega
  have hlt_bob : tr_bob.length < ((Move.bobStart b_bob a_bob kh regIdxA mh pqIdx spqrMsgIdx sh_bob).next tr_bob).length := by dsimp only [tr_bob]; rw [hnext_bob]; exact length_lt_bobStartTr w_bob
  have hrnd_bob : (((Move.bobStart b_bob a_bob kh regIdxA mh pqIdx spqrMsgIdx sh_bob).next tr_bob).at? tr_bob.length :
      Option DY.Random.ExecEntryT) = some (TR.RndE 32) := by
    dsimp only [tr_bob]; rw [hnext_bob, at?_rnd_bobStartTr w_bob]; simp
  refine ⟨ms₄₀, pre₃, post₃, b_bob, a_bob, kh, regIdxA, mh, pqIdx, spqrMsgIdx, sh_bob, tr_bob, w_bob,
    by rw [hms₄₃]; simp only [List.append_assoc], hmp₄₀, rfl, hpre₃, hpost₃, hnext_bob,
    gamma_rng_of_bobVis_forall2 hsh3 hlt_bob hrnd_bob hm_bob'⟩
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.TraceFacts in
theorem not_tr4_state_for_call5' {r : Records} {S : Sem} {g : Ghost} {tr₁ tr₂ tr₃ tr_bob tr₅ : ExecTrace} {cl₁ e₁ c₁ cl₂ cl₅ e₅ c₅ : Nat} {b_bob a_bob : Participant} {kh : DY.Libsignal.PQXDH.BobKeyHandles} {regIdxA : Nat} {mh : DY.Libsignal.PQXDH.PreKeyMsgHandles} {pqIdx : Nat} {spqrMsgIdx : UInt32} (w_bob : BobStartOk tr_bob b_bob a_bob kh regIdxA mh pqIdx spqrMsgIdx) {o₁ : DY.Libsignal.PQXDH.AliceHandshakeOut} {stA₁ : DY.Libsignal.TripleRatchet.TRState} (hstA₁ : stA₁ = aliceStartState tr₁ r.bob o₁) (hsm₁ : CompRPreKeyWire.SendMatchesMoves compI0 r S g (sendAt 37) (received tr₂ [e₁, c₁] ++ [encOut tr₂ stA₁ cl₁ (tr₂.length + 2)])) (hγ_rng41 : gamma compI0 S g (randTerm tr_bob.length 32) = rngAt 41) {st₅ : DY.Libsignal.TripleRatchet.TRState} (hst₅_cases : st₅ = bobFinalSt tr_bob a_bob w_bob ∨ st₅ = encSt tr₃ (encSt tr₂ stA₁ cl₁) cl₂ ∨ st₅ = encSt tr₂ stA₁ cl₁ ∨ st₅ = stA₁) (hsm₅ : CompRPreKeyWire.SendMatchesMoves compI0 r S g (sendAt 80) (received tr₅ [e₅, c₅] ++ [encOut tr₅ st₅ cl₅ (tr₅.length + 2)])) : False := by
  obtain ⟨q₅, hq₅⟩ := sendAt80_parses; obtain ⟨_, _, -, -, -, hmsg₅⟩ := CompRX0Mem.sendMatches_append_inv hsm₅ sendAt80_len hq₅; have hcan₅ := sendAt80_canon hq₅
  have hns₁ : stA₁.ns = 0 := by rw [hstA₁]; rfl
  have hpn₁ : stA₁.pn = 0 := by rw [hstA₁]; rfl
  rcases hst₅_cases with rfl | rfl | rfl | hst₅_eq
  · obtain ⟨_, -, -, hsrk₅⟩ := WsIdx1PreKeyRep.faithfulInner_of_gamma_encOut_generic
      compI0 S g tr₅ (bobFinalSt tr_bob a_bob w_bob) cl₅ (tr₅.length + 2) q₅
      (bobFinalSt_ns_eq w_bob) (bobFinalSt_pn_eq w_bob) hmsg₅.symm hcan₅
    rw [bobFinalSt_dhs_eq w_bob, CompFreshDistinct.gamma_dhPk_compI0, hγ_rng41] at hsrk₅; exact sendAt80_srk_ne_rng41 hq₅ hsrk₅.symm
  · exact not_gamma_encOut_ns2_at0 S g tr₅ _ cl₅ (tr₅.length + 2) q₅
      (by rw [encSt_ns_eq, encSt_ns_eq, hns₁]; rfl) (by rw [encSt_pn_eq, encSt_pn_eq, hpn₁]) hmsg₅.symm hcan₅
  · exact not_gamma_encOut_ns1_at0 S g tr₅ _ cl₅ (tr₅.length + 2) q₅
      (by rw [encSt_ns_eq, hns₁]; rfl) (by rw [encSt_pn_eq, hpn₁]) hmsg₅.symm hcan₅
  · subst hst₅_eq
    obtain ⟨q₁, hq₁⟩ := sendAt37_parses; obtain ⟨_, _, -, -, -, hmsg₁⟩ := CompRX0Mem.sendMatches_append_inv hsm₁ sendAt37_len hq₁; have hcan₁ := sendAt37_canon hq₁; obtain ⟨_, -, -, hsrk₅⟩ := WsIdx1PreKeyRep.faithfulInner_of_gamma_encOut_generic compI0 S g tr₅ st₅ cl₅ (tr₅.length + 2) q₅ hns₁ hpn₁ hmsg₅.symm hcan₅; obtain ⟨_, -, -, hsrk₁⟩ := WsIdx1PreKeyRep.faithfulInner_of_gamma_encOut_generic compI0 S g tr₂ st₅ cl₁ (tr₂.length + 2) q₁ hns₁ hpn₁ hmsg₁.symm hcan₁
    exact sendAt80_srk_ne_sendAt37 hq₅ hq₁ (hsrk₅.symm.trans hsrk₁)
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.TraceFacts in
theorem decomp45_raw {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {τ₄₃ b5 : List MachineEvent}
    (hc5 : DY.Libsignal.Composed.Refinement.Cli.CoinSplit [.pt (ptAt 78), .rng (rngAt 79), .send (sendAt 80)] b5)
    (hmp : Symbolic.Swarm.CREF.MatchedPrefix compI0 r S g ms ((τ₄₃ ++ seg 43 35) ++ b5)) :
    ∃ (ms₄₃ pre₄ mid₅ post₅ : List Move) (m₄ : Move) (me₅ : Participant) (sIdx₅ cl₅ pq₅ e₅ c₅ : Nat) (tr₄ tr₅ : ExecTrace), ms = ms₄₃ ++ pre₄ ++ m₄ :: mid₅ ++ Move.encrypt me₅ sIdx₅ cl₅ pq₅ (some (e₅, c₅)) :: post₅ ∧ Symbolic.Swarm.CREF.MatchedPrefix compI0 r S g ms₄₃ τ₄₃ ∧ tr₄ = (runMoves pre₄ (runTraceMoves r ms₄₃)).1 ∧ tr₅ = (runMoves mid₅ (m₄.next tr₄)).1 ∧ m₄.isSetup = false ∧ m₄.Anchored tr₄ ∧ MovesFrom InvisibleNoEffect (runTraceMoves r ms₄₃) pre₄ ∧ MovesFrom InvisibleNoEffect (m₄.next tr₄) mid₅ ∧ MovesFrom InvisibleNoEffect ((Move.encrypt me₅ sIdx₅ cl₅ pq₅ (some (e₅, c₅))).next tr₅) post₅ ∧ lastSent tr₅ ((Move.encrypt me₅ sIdx₅ cl₅ pq₅ (some (e₅, c₅))).next tr₅) ≠ none ∧ List.Forall₂ (EventMatchesEntry compI0 r S g) (.recv (wireAt 43) :: rs4) (m₄.vis tr₄) ∧ List.Forall₂ (EventMatchesEntry compI0 r S g) b5 (encVis tr₅ ((Move.encrypt me₅ sIdx₅ cl₅ pq₅ (some (e₅, c₅))).next tr₅) (some (e₅, c₅)) true) := by
  obtain ⟨pieces₅, _, _, hb5⟩ := CliCoinSplit.coinSplit_send_exit0_inv hc5
  let blk₁ : List MachineEvent := .recv (wireAt 43) :: rs4
  have hmp81 : Symbolic.Swarm.CREF.MatchedPrefix compI0 r S g ms ((τ₄₃ ++ blk₁) ++ b5) := by
    dsimp only [blk₁]; rwa [← seg43_shape]
  have hhead₂ : ∀ e ∈ b5.head?, eventKind e = .recv ∨ eventKind e = .pt := by intro e he; simp [hb5] at he; subst he; exact Or.inr rfl
  obtain ⟨ms₇₈, δ₂, hms, hmp₇₈, hfor₂⟩ := matchedPrefix6_split hmp81 hhead₂ (CompPrefixInvStruct.matchedPrefix6_prefix_reachable hmp81); have hB₂ : XplBlock6 compI0 r S g ms₇₈ δ₂ _ b5 := ⟨hmp₇₈, hms ▸ hmp81.2.1, hfor₂⟩
  have hhead₁ : ∀ e ∈ blk₁.head?, eventKind e = .recv ∨ eventKind e = .pt := by intro e he; simp [blk₁] at he; subst he; exact Or.inl rfl
  obtain ⟨ms₄₃, δ₁, hms₁, hmp₄₃, hfor₁⟩ := matchedPrefix6_split hmp₇₈ hhead₁ (CompPrefixInvStruct.matchedPrefix6_prefix_reachable hmp₇₈); have hB₁ : XplBlock6 compI0 r S g ms₄₃ δ₁ _ blk₁ := ⟨hmp₄₃, hms₁ ▸ hmp₇₈.2.1, hfor₁⟩
  have htail₁ : ∀ e ∈ blk₁.tail, eventKind e ≠ .recv ∧ eventKind e ≠ .pt ∧ eventKind e ≠ .leak := by intro e he; have hk := rs4_kind e he; rw [hk]; decide
  obtain ⟨pre₄, m₄, post₄, rfl, hpre₄, ⟨hs₄, ha₄, hm₄⟩, hpost₄⟩ :=
    xpl6_oneMove hB₁ hhead₁ (by simp [blk₁]) htail₁
  have htail₂ : ∀ e ∈ b5.tail, eventKind e ≠ .recv ∧ eventKind e ≠ .pt ∧ eventKind e ≠ .leak := by
    intro e he; simp only [hb5, List.tail_cons, List.mem_append, List.mem_map, List.mem_singleton] at he
    rcases he with ⟨_, _, rfl⟩ | rfl <;> { dsimp [eventKind]; decide }
  obtain ⟨pre₅, m₅, post₅, rfl, hpre₅, ⟨_, _, hm₅⟩, hpost₅⟩ :=
    xpl6_oneMove hB₂ hhead₂ (by simp [hb5]) htail₂
  obtain ⟨tr₄, htr₄⟩ : ∃ tr₄, tr₄ = (runMoves pre₄ (runTraceMoves r ms₄₃)).1 := ⟨_, rfl⟩
  let mid₅ := post₄ ++ pre₅
  have hrun_ms₇₈ : runTraceMoves r ms₇₈ = (runMoves post₄ (m₄.next tr₄)).1 := by rw [hms₁, xpl_runTrace_eq, runMoves_append_fst, ← xpl_runTrace_eq r ms₄₃, runMoves_append_fst, runMoves_cons_fst₀, ← htr₄]
  obtain ⟨tr₅, htr₅⟩ : ∃ tr₅, tr₅ = (runMoves mid₅ (m₄.next tr₄)).1 := ⟨_, rfl⟩
  have htr₅_eq : (runMoves pre₅ (runTraceMoves r ms₇₈)).1 = tr₅ := by rw [htr₅, hrun_ms₇₈, ← runMoves_append_fst]
  rw [htr₅_eq] at hm₅ hpost₅; rw [← htr₄] at ha₄ hm₄ hpost₄
  have hmid₅ : MovesFrom InvisibleNoEffect (m₄.next tr₄) mid₅ := by rw [movesFrom_append, ← hrun_ms₇₈]; exact ⟨hpost₄, hpre₅⟩
  have hmem_send₅ : MachineEvent.send (sendAt 80) ∈ b5 := by simp [hb5]
  obtain ⟨me₅, sIdx₅, cl₅, pq₅, wrap₅, rfl, hls₅, hwrap_none₅, hm₅_vis⟩ :=
    CliCoinSplit.invert_send_move_split hmem_send₅ hm₅
  cases wrap₅ with
  | none =>
    exfalso; have hw80 := sendAt80_head?; rw [hwrap_none₅ rfl] at hw80; cases hw80
  | some wr₅ =>
    rcases wr₅ with ⟨e₅, c₅⟩
    exact ⟨ms₄₃, pre₄, mid₅, post₅, m₄, me₅, sIdx₅, cl₅, pq₅, e₅, c₅, tr₄, tr₅,
      by simp [hms, hms₁, mid₅, List.append_assoc],
      hmp₄₃, htr₄, htr₅, hs₄, ha₄, hpre₄, hmid₅, hpost₅, hls₅, hm₄, hm₅_vis⟩
theorem at?_pqSt_iniAliceStartTr (tr : ExecTrace) (a b : Participant) (o : DY.Libsignal.PQXDH.AliceHandshakeOut) (j : Nat) : ((iniAliceStartTr tr a b o).at? j : Option PQXDHStEntry) = (tr.at? j : Option PQXDHStEntry) := by
  unfold iniAliceStartTr; dsimp only
  rw [CompPrefixInvAlice.at?_append_other_eq _ (TRStE _ _) rfl, CompPrefixInvAlice.at?_append_other_eq _ (CEvE _) rfl, CompPrefixInvAlice.at?_append_other_eq _ (TREvE _) rfl, CompPrefixInvAlice.at?_append_other_eq _ (PQEvE _) rfl, CompPrefixInvAlice.at?_append_other_eq _ (NetE _) rfl, CompPrefixInvAlice.at?_append_other_eq _ (NetE _) rfl, CompPrefixInvAlice.at?_append_other_eq _ (RndE _) rfl, CompPrefixInvAlice.at?_append_other_eq _ (RndE _) rfl, CompPrefixInvAlice.at?_append_other_eq _ (RndE _) rfl]
theorem at?_pqSt_aliceStartTrOfOut (tr : ExecTrace) (a b : Participant) (o : DY.Libsignal.PQXDH.AliceHandshakeOut) (j : Nat) : ((aliceStartTrOfOut tr a b o).at? j : Option PQXDHStEntry) = (tr.at? j : Option PQXDHStEntry) := at?_pqSt_iniAliceStartTr tr a b o j
theorem at?_pqSt_encNextTr (tr₂ : ExecTrace) (me : Participant) (sIdx : Nat) (stA : DY.Libsignal.TripleRatchet.TRState) (cl pq j : Nat) : ((encNextTr tr₂ me sIdx stA cl pq).at? j : Option PQXDHStEntry) = (tr₂.at? j : Option PQXDHStEntry) := by
  unfold encNextTr encPreSaltTr; dsimp only
  rw [CompPrefixInvAlice.at?_append_other_eq _ (NetE _) rfl, CompPrefixInvAlice.at?_append_other_eq _ (TRStE _ _) rfl, CompPrefixInvAlice.at?_append_other_eq _ (TREvE _) rfl, CompPrefixInvAlice.at?_append_other_eq _ (TREvE _) rfl, CompPrefixInvAlice.at?_append_other_eq _ (NetE _) rfl, CompPrefixInvAlice.at?_append_other_eq _ (RndE _) rfl, CompPrefixInvAlice.at?_append_other_eq _ (RndE _) rfl]
theorem prefix_hyps_of_modelRun {r : Records} {ms P Q : List Move} (hrun : ModelRun r ms) (hms : ms = P ++ Q) : (∀ m ∈ P, m.isSetup = false) ∧ MovesAnchored P (setupTrace r) := by
  obtain ⟨_, hns, ⟨_, hanc, _⟩, _, _⟩ := hrun; rw [hms, b5_movesAnchored_append] at hanc
  exact ⟨fun m hm => hns m (hms ▸ List.mem_append_left _ hm), hanc.1⟩
theorem at?_pqSt_of_movesFrom_invisible {tr : ExecTrace} {δ : List Move} (hs : ∀ m ∈ δ, m.isSetup = false) (ha : MovesAnchored δ tr) (hδ : MovesFrom InvisibleNoEffect tr δ) (j : Nat) : (((runMoves δ tr).1).at? j : Option PQXDHStEntry) = (tr.at? j : Option PQXDHStEntry) := by
  induction δ generalizing tr with
  | nil => rfl
  | cons m δ ih =>
    simp only [runMoves]; rw [ih (fun m' hm' => hs m' (List.mem_cons_of_mem _ hm')) ha.2 hδ.2]
    rcases CompPrefixInvBundle.next_of_isSetup_false_vis_nil
        (hs m (List.mem_cons_self ..)) ha.1 hδ.1.1 with h | ⟨t, h⟩ | ⟨ev, h⟩
    · rw [h]
    · rw [h, CompPrefixInvAlice.at?_append_other_eq tr (⟨t⟩ : DY.Network.ExecEntryT) rfl j]
    · rw [h, CompPrefixInvAlice.at?_append_other_eq tr (⟨ev⟩ : DY.ProtocolEvent.ExecEntryT DY.Libsignal.PQXDH.PQXDHEvent) rfl j]
theorem at?_pqSt_step {tr tr' : ExecTrace} {δ rest : List Move} {m : Move} (hs : ∀ x ∈ δ ++ m :: rest, x.isSetup = false) (ha : MovesAnchored (δ ++ m :: rest) tr) (hδ : MovesFrom InvisibleNoEffect tr δ) (htr' : tr' = (runMoves δ tr).1) : (∀ j, (tr'.at? j : Option PQXDHStEntry) = (tr.at? j : Option PQXDHStEntry)) ∧ (∀ x ∈ rest, x.isSetup = false) ∧ MovesAnchored rest (m.next tr') := by
  rw [b5_movesAnchored_append, ← htr'] at ha
  refine ⟨fun j => ?_, fun x hx => hs x (List.mem_append_right _ (List.mem_cons_of_mem _ hx)), ha.2.2⟩
  rw [htr']; exact at?_pqSt_of_movesFrom_invisible (fun x hx => hs x (List.mem_append_left _ hx)) ha.1 hδ j
theorem at?_pqSt_tr4_of_chain {r : Records} {pre₀ mid₁ mid₂ mid₃ mid₄ : List Move} {m₀ m₁ m₂ m₃ : Move} {tr₁ tr₂ tr₃ tr_bob tr₄ : ExecTrace} {o₁ : DY.Libsignal.PQXDH.AliceHandshakeOut} {stA₁ : DY.Libsignal.TripleRatchet.TRState} {cl₁ cl₂ : Nat} {b_bob a_bob : Participant} {kh : DY.Libsignal.PQXDH.BobKeyHandles} {regIdxA : Nat} {mh : DY.Libsignal.PQXDH.PreKeyMsgHandles} {pqIdx : Nat} {spqrMsgIdx : UInt32} (w_bob : BobStartOk tr_bob b_bob a_bob kh regIdxA mh pqIdx spqrMsgIdx) (hs₀ : ∀ x ∈ pre₀ ++ (m₀ :: (mid₁ ++ (m₁ :: (mid₂ ++ (m₂ :: (mid₃ ++ (m₃ :: mid₄))))))), x.isSetup = false) (ha₀ : MovesAnchored (pre₀ ++ (m₀ :: (mid₁ ++ (m₁ :: (mid₂ ++ (m₂ :: (mid₃ ++ (m₃ :: mid₄)))))))) (setupTrace r)) (htr₁ : tr₁ = (runMoves pre₀ (setupTrace r)).1) (htr₂ : tr₂ = (runMoves mid₁ (m₀.next tr₁)).1) (htr₃ : tr₃ = (runMoves mid₂ (m₁.next tr₂)).1) (htr_bob : tr_bob = (runMoves mid₃ (m₂.next tr₃)).1) (htr₄ : tr₄ = (runMoves mid₄ (m₃.next tr_bob)).1) (hm₀ : m₀.next tr₁ = aliceStartTrOfOut tr₁ r.alice r.bob o₁) (hE₁ : m₁.next tr₂ = encNextTr tr₂ r.alice (tr₁.length + 8) stA₁ cl₁ (tr₂.length + 2)) (hE₂ : m₂.next tr₃ = encNextTr tr₃ r.alice (tr₂.length + 5) (encSt tr₂ stA₁ cl₁) cl₂ (tr₃.length + 2)) (hnext_bob : m₃.next tr_bob = bobStartTr tr_bob b_bob a_bob w_bob) (hpre₀ : MovesFrom InvisibleNoEffect (setupTrace r) pre₀) (hmid₁ : MovesFrom InvisibleNoEffect (m₀.next tr₁) mid₁) (hmid₂ : MovesFrom InvisibleNoEffect (m₁.next tr₂) mid₂) (hmid₃ : MovesFrom InvisibleNoEffect (m₂.next tr₃) mid₃) (hmid₄ : MovesFrom InvisibleNoEffect (m₃.next tr_bob) mid₄) (j : Nat) : (tr₄.at? j : Option PQXDHStEntry) = ((setupTrace r).at? j : Option PQXDHStEntry) := by
  obtain ⟨hpq₁, hs₁, ha₁⟩ := at?_pqSt_step hs₀ ha₀ hpre₀ htr₁
  obtain ⟨hpq₂, hs₂, ha₂⟩ := at?_pqSt_step hs₁ ha₁ hmid₁ htr₂
  obtain ⟨hpq₃, hs₃, ha₃⟩ := at?_pqSt_step hs₂ ha₂ hmid₂ htr₃
  obtain ⟨hpq_bob, hs₄, ha₄⟩ := at?_pqSt_step hs₃ ha₃ hmid₃ htr_bob
  have hpq₄ : (tr₄.at? j : Option PQXDHStEntry) = ((m₃.next tr_bob).at? j : Option PQXDHStEntry) := by
    rw [htr₄]; exact at?_pqSt_of_movesFrom_invisible hs₄ ha₄ hmid₄ j
  rw [hpq₄, hnext_bob, at?_pqSt_bobStartTr w_bob j, hpq_bob j, hE₂, at?_pqSt_encNextTr _ _ _ _ _ _ j, hpq₃ j, hE₁, at?_pqSt_encNextTr _ _ _ _ _ _ j, hpq₂ j, hm₀, at?_pqSt_aliceStartTrOfOut _ _ _ _ j, hpq₁ j]
theorem a_out_eq : @CompPrefixInvAlice.iniAliceOut = @CompTrace.aliceOut := rfl
theorem a_st_eq : @CompPrefixInvAlice.iniAliceStartState = @CompPrefixInvBundle.aliceStartState := rfl
theorem at?_trSt_tr4_of_chain {r : Records} {pre₀ mid₁ mid₂ mid₃ mid₄ : List Move} {m₀ m₁ m₂ m₃ : Move} {tr₁ tr₂ tr₃ tr_bob tr₄ : ExecTrace} {o₁ : DY.Libsignal.PQXDH.AliceHandshakeOut} {stA₁ : DY.Libsignal.TripleRatchet.TRState} {cl₁ cl₂ : Nat} {b_bob a_bob : Participant} {kh : DY.Libsignal.PQXDH.BobKeyHandles} {regIdxA : Nat} {mh : DY.Libsignal.PQXDH.PreKeyMsgHandles} {pqIdx : Nat} {spqrMsgIdx : UInt32} (w_bob : BobStartOk tr_bob b_bob a_bob kh regIdxA mh pqIdx spqrMsgIdx) (htr₁ : tr₁ = (runMoves pre₀ (setupTrace r)).1) (hstA₁ : stA₁ = aliceStartState tr₁ r.bob o₁) (htr₂ : tr₂ = (runMoves mid₁ (m₀.next tr₁)).1) (htr₃ : tr₃ = (runMoves mid₂ (m₁.next tr₂)).1) (htr_bob : tr_bob = (runMoves mid₃ (m₂.next tr₃)).1) (htr₄ : tr₄ = (runMoves mid₄ (m₃.next tr_bob)).1) (hm₀ : m₀.next tr₁ = aliceStartTrOfOut tr₁ r.alice r.bob o₁) (hE₁ : m₁.next tr₂ = encNextTr tr₂ r.alice (tr₁.length + 8) stA₁ cl₁ (tr₂.length + 2)) (hE₂ : m₂.next tr₃ = encNextTr tr₃ r.alice (tr₂.length + 5) (encSt tr₂ stA₁ cl₁) cl₂ (tr₃.length + 2)) (hnext_bob : m₃.next tr_bob = bobStartTr tr_bob b_bob a_bob w_bob) (hpre₀ : MovesFrom InvisibleNoEffect (setupTrace r) pre₀) (hmid₁ : MovesFrom InvisibleNoEffect (m₀.next tr₁) mid₁) (hmid₂ : MovesFrom InvisibleNoEffect (m₁.next tr₂) mid₂) (hmid₃ : MovesFrom InvisibleNoEffect (m₂.next tr₃) mid₃) (hmid₄ : MovesFrom InvisibleNoEffect (m₃.next tr_bob) mid₄) (j : Nat) : (tr₄.at? j : Option TRStEntry) = if j = (bobStartTr tr_bob b_bob a_bob w_bob).length - 1 then some (TRStE b_bob (bobFinalSt tr_bob a_bob w_bob)) else if j = tr₃.length + 5 then some (TRStE r.alice (encSt tr₃ (encSt tr₂ stA₁ cl₁) cl₂)) else if j = tr₂.length + 5 then some (TRStE r.alice (encSt tr₂ stA₁ cl₁)) else if j = tr₁.length + 8 then some (TRStE r.alice stA₁) else none := by
  have hntr₁ : NoTRState tr₁ := by rw [htr₁]; exact noTRState_of_movesFrom_invisibleNoEffect (noTRState_setupTrace r) hpre₀
  have h0 : ((aliceStartTrOfOut tr₁ r.alice r.bob o₁).at? j : Option TRStEntry) =
      if j = tr₁.length + 8 then some (TRStE r.alice stA₁) else none := by
    rw [← a_tr_eq, hstA₁, ← a_st_eq]; exact at?_trSt_iniAliceStartTr_of_noTRState hntr₁ r.alice r.bob o₁ j
  have hat_tr_bob : (tr_bob.at? j : Option TRStEntry) =
      if j = tr₃.length + 5 then some (TRStE r.alice (encSt tr₃ (encSt tr₂ stA₁ cl₁) cl₂))
      else if j = tr₂.length + 5 then some (TRStE r.alice (encSt tr₂ stA₁ cl₁))
      else if j = tr₁.length + 8 then some (TRStE r.alice stA₁) else none := by
    rw [htr_bob, at?_trSt_of_movesFrom_invisibleNoEffect hmid₃, hE₂, at?_trSt_encNextTr', htr₃, at?_trSt_of_movesFrom_invisibleNoEffect hmid₂, hE₁, at?_trSt_encNextTr', htr₂, at?_trSt_of_movesFrom_invisibleNoEffect hmid₁, hm₀, h0]
  rw [htr₄, at?_trSt_of_movesFrom_invisibleNoEffect hmid₄, hnext_bob, at?_trSt_bobStartTr w_bob, hat_tr_bob]
theorem sendMatches_of_eventMatchesEntry_send {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {w : HwBytes} {L : List DY.Bytes} (h : EventMatchesEntry i r S g (.send w) ⟨.send, L, .preKeySend, none⟩) : CompRPreKeyWire.SendMatchesMoves i r S g w L := h.2
theorem coinSplit_send_no_leak {pt c w : HwBytes} {b : List MachineEvent}
    (hc : DY.Libsignal.Composed.Refinement.Cli.CoinSplit [.pt pt, .rng c, .send w] b) :
    ∀ e ∈ b, eventKind e ≠ .leak := by
  obtain ⟨pieces, _, _, rfl⟩ := CliCoinSplit.coinSplit_send_exit0_inv hc
  intro e he
  simp only [List.mem_cons, List.mem_append, List.mem_map, List.not_mem_nil, or_false] at he
  rcases he with rfl | ⟨_, _, rfl⟩ | rfl <;> nofun
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.TraceFacts in
theorem seg_no_leak (k n : Nat) : ∀ e ∈ seg k n, eventKind e ≠ .leak :=
  fun e he => Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.NoFull.trace_no_leak e
    (List.mem_of_mem_drop (List.mem_of_mem_take he))
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.TraceFacts in
theorem split81_no_leak {b1 b2 b5 : List MachineEvent}
    (hc1 : DY.Libsignal.Composed.Refinement.Cli.CoinSplit [.pt (ptAt 35), .rng (rngAt 36), .send (sendAt 37)] b1)
    (hc2 : DY.Libsignal.Composed.Refinement.Cli.CoinSplit WsIdx1CensusDefs.seg38SplitSrc b2)
    (hc5 : DY.Libsignal.Composed.Refinement.Cli.CoinSplit [.pt (ptAt 78), .rng (rngAt 79), .send (sendAt 80)] b5) :
    ∀ e ∈ (((((seg 0 35 ++ b1) ++ b2) ++ seg 40 3) ++ seg 43 35) ++ b5), eventKind e ≠ .leak := by
  intro e he
  simp only [List.mem_append] at he
  rcases he with (((((h | h) | h) | h) | h) | h)
  · exact seg_no_leak 0 35 e h
  · exact coinSplit_send_no_leak hc1 e h
  · exact coinSplit_send_no_leak hc2 e h
  · exact seg_no_leak 40 3 e h
  · exact seg_no_leak 43 35 e h
  · exact coinSplit_send_no_leak hc5 e h
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.TraceFacts in
set_option maxHeartbeats 400000 in
theorem decomp81_full {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {b1 b2 b5 : List MachineEvent}
    (hfits : compFitsPinned Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1.setup compI0 r)
    (hnb : CompSetupSecrecy.NoBrk r ms)
    (hc1 : DY.Libsignal.Composed.Refinement.Cli.CoinSplit [.pt (ptAt 35), .rng (rngAt 36), .send (sendAt 37)] b1)
    (hc2 : DY.Libsignal.Composed.Refinement.Cli.CoinSplit WsIdx1CensusDefs.seg38SplitSrc b2)
    (hc5 : DY.Libsignal.Composed.Refinement.Cli.CoinSplit [.pt (ptAt 78), .rng (rngAt 79), .send (sendAt 80)] b5)
    (hmp : Symbolic.Swarm.CREF.MatchedPrefix compI0 r S g ms (((((seg 0 35 ++ b1) ++ b2) ++ seg 40 3) ++ seg 43 35) ++ b5)) :
    ∃ (pre₀ mid₁ mid₂ mid₃ mid₄ mid₅ post₅ : List Move) (hb₀ hb₄ : DY.Libsignal.PQXDH.BundleHandles) (sh₀ sh₄ cl₁ e₁ c₁ cl₂ e₂ c₂ cl₅ e₅ c₅ : Nat) (b_bob a_bob : Participant) (kh : DY.Libsignal.PQXDH.BobKeyHandles) (regIdxA : Nat) (mh : DY.Libsignal.PQXDH.PreKeyMsgHandles) (pqIdx : Nat) (spqrMsgIdx : UInt32) (sh_bob : Nat) (tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ : ExecTrace) (w_bob : BobStartOk tr_bob b_bob a_bob kh regIdxA mh pqIdx spqrMsgIdx) (o₁ o₂ : DY.Libsignal.PQXDH.AliceHandshakeOut) (stA₁ stA₂ : DY.Libsignal.TripleRatchet.TRState),
      let m₀ := Move.aliceStart r.alice r.bob 4 6 hb₀ sh₀
      let m₁ := Move.encrypt r.alice (tr₁.length + 8) cl₁ (tr₂.length + 2) (some (e₁, c₁))
      let m₂ := Move.encrypt r.alice (tr₂.length + 5) cl₂ (tr₃.length + 2) (some (e₂, c₂))
      let m₃ := Move.bobStart b_bob a_bob kh regIdxA mh pqIdx spqrMsgIdx sh_bob
      let m₄ := Move.aliceStart r.alice r.bob 4 6 hb₄ sh₄
      let m₅ := Move.encrypt r.alice (tr₄.length + 8) cl₅ (tr₅.length + 2) (some (e₅, c₅))
      tr₁ = (runMoves pre₀ (setupTrace r)).1 ∧
      o₁ = aliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none ∧
      stA₁ = aliceStartState tr₁ r.bob o₁ ∧ tr₂ = (runMoves mid₁ (m₀.next tr₁)).1 ∧
      tr₃ = (runMoves mid₂ (m₁.next tr₂)).1 ∧ tr_bob = (runMoves mid₃ (m₂.next tr₃)).1 ∧
      tr₄ = (runMoves mid₄ (m₃.next tr_bob)).1 ∧
      o₂ = aliceOut tr₄ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none ∧
      stA₂ = aliceStartState tr₄ r.bob o₂ ∧ tr₅ = (runMoves mid₅ (m₄.next tr₄)).1 ∧
      ms = pre₀ ++ m₀ :: mid₁ ++ m₁ :: mid₂ ++ m₂ :: mid₃ ++ m₃ :: mid₄ ++ m₄ :: mid₅ ++ m₅ :: post₅ ∧
      m₀.next tr₁ = aliceStartTrOfOut tr₁ r.alice r.bob o₁ ∧
      m₁.next tr₂ = encNextTr tr₂ r.alice (tr₁.length + 8) stA₁ cl₁ (tr₂.length + 2) ∧
      m₂.next tr₃ = encNextTr tr₃ r.alice (tr₂.length + 5) (encSt tr₂ stA₁ cl₁) cl₂ (tr₃.length + 2) ∧
      m₃.next tr_bob = bobStartTr tr_bob b_bob a_bob w_bob ∧
      m₄.next tr₄ = aliceStartTrOfOut tr₄ r.alice r.bob o₂ ∧
      m₅.next tr₅ = encNextTr tr₅ r.alice (tr₄.length + 8) stA₂ cl₅ (tr₅.length + 2) ∧
      MovesFrom InvisibleNoEffect (setupTrace r) pre₀ ∧ MovesFrom InvisibleNoEffect (m₀.next tr₁) mid₁ ∧
      MovesFrom InvisibleNoEffect (m₁.next tr₂) mid₂ ∧ MovesFrom InvisibleNoEffect (m₂.next tr₃) mid₃ ∧
      MovesFrom InvisibleNoEffect (m₃.next tr_bob) mid₄ ∧ MovesFrom InvisibleNoEffect (m₄.next tr₄) mid₅ ∧
      MovesFrom InvisibleNoEffect (m₅.next tr₅) post₅ ∧
      NetMsgAt o₁.ek (tr₁.length + 3) tr₂ ∧ NetMsgAt o₁.ct (tr₁.length + 4) tr₂ ∧
      NetMsgAt o₂.ek (tr₄.length + 3) tr₅ ∧ NetMsgAt o₂.ct (tr₄.length + 4) tr₅ ∧
      List.Forall₂ (EventMatchesEntry compI0 r S g) (.recv (wireAt 0) :: rs0) (aliceVis tr₁ (m₀.next tr₁) hb₀) ∧
      List.Forall₂ (EventMatchesEntry compI0 r S g) (.recv (wireAt 43) :: rs4) (aliceVis tr₄ (m₄.next tr₄) hb₄) ∧
      CompRPreKeyWire.SendMatchesMoves compI0 r S g (sendAt 37) (received tr₂ [e₁, c₁] ++ [encOut tr₂ stA₁ cl₁ (tr₂.length + 2)]) ∧
      CompRPreKeyWire.SendMatchesMoves compI0 r S g (wireAt 40) (received tr₃ [e₂, c₂] ++ [encOut tr₃ (encSt tr₂ stA₁ cl₁) cl₂ (tr₃.length + 2)]) ∧
      CompRPreKeyWire.SendMatchesMoves compI0 r S g (sendAt 80) (received tr₅ [e₅, c₅] ++ [encOut tr₅ stA₂ cl₅ (tr₅.length + 2)]) := by
  rcases hfits.1 with ⟨hwf, -, -, -, -, -, -, hsb1, hsb2, -, -, -, -, hEq, -⟩
  have hNe : r.alice ≠ r.bob := hwf.1
  have hc : Compat compI0 r S g := hmp.1
  have hown : ownSaltsFrom (setupTrace r) ms = true := hmp.2.1.2.2.2.2.1
  obtain ⟨ms₄₃, pre₄, mid₅, post₅, m₄, me₅, sIdx₅, cl₅, pq₅, e₅, c₅, tr₄, tr₅,
    hms, hmp₄₃, htr₄_raw, htr₅, hs₄, ha₄, hpre₄, hmid₅, hpost₅, hls₅, hm₄, hm₅_vis⟩ := decomp45_raw hc5 hmp
  obtain ⟨ms₄₀, pre₃, post₃, b_bob, a_bob, kh, regIdxA, mh, pqIdx, spqrMsgIdx, sh_bob, tr_bob, w_bob,
    hms₄₃, hmp₄₀, htr_bob_eq, hpre₃, hpost₃, hnext_bob, hγ_rng41⟩ := decomp43_step hc1 hc2 hmp₄₃
  have hmp₄₀' : Symbolic.Swarm.CREF.MatchedPrefix compI0 r S g ms₄₀ (((.recv (wireAt 0) :: WsIdx1Decomp40.rs0) ++ b1) ++ b2) := hmp₄₀
  have hnb₄₃ : CompSetupSecrecy.NoBrk r ms₄₃ :=
    CompRX0Top.noBrk_append_left (ms₂ := pre₄ ++ m₄ :: mid₅ ++ Move.encrypt me₅ sIdx₅ cl₅ pq₅ (some (e₅, c₅)) :: post₅) (by rw [← List.append_assoc, ← List.append_assoc, ← hms]; exact hnb)
  have hnb₄₀ : CompSetupSecrecy.NoBrk r ms₄₀ :=
    CompRX0Top.noBrk_append_left (ms₂ := pre₃ ++ Move.bobStart b_bob a_bob kh regIdxA mh pqIdx spqrMsgIdx sh_bob :: post₃) (by rw [← List.append_assoc, ← hms₄₃]; exact hnb₄₃)
  obtain ⟨pre₀, mid₁, mid₂, post₂, hb₀, sh₀, cl₁, e₁, c₁, cl₂, e₂, c₂, tr₁, tr₂, tr₃, o₁, stA₁, htr₁, ho₁, hstA₁, htr₂, htr₃, hms₄₀, hm₀, hE₁, hE₂, hpre₀, hmid₁, hmid₂, hpost₂,
    hek₁, hct₁, hvis₀, hsm₁, hsm₂⟩ := decomp40_full hfits hnb₄₀ hc1 hc2 hmp₄₀'
  set m₀ := Move.aliceStart r.alice r.bob 4 6 hb₀ sh₀
  set m₁ := Move.encrypt r.alice (tr₁.length + 8) cl₁ (tr₂.length + 2) (some (e₁, c₁))
  set m₂ := Move.encrypt r.alice (tr₂.length + 5) cl₂ (tr₃.length + 2) (some (e₂, c₂))
  set m₃ := Move.bobStart b_bob a_bob kh regIdxA mh pqIdx spqrMsgIdx sh_bob
  obtain ⟨mid₃, hmid₃_def⟩ : ∃ mid₃, mid₃ = post₂ ++ pre₃ := ⟨_, rfl⟩
  obtain ⟨mid₄, hmid₄_def⟩ : ∃ mid₄, mid₄ = post₃ ++ pre₄ := ⟨_, rfl⟩
  have hrun_ms₄₀ : runTraceMoves r ms₄₀ = (runMoves post₂ (m₂.next tr₃)).1 := by
    rw [hms₄₀, xpl_runTrace_eq]
    simp only [List.append_assoc, List.cons_append, runMoves_append_fst, runMoves_cons_fst₀, ← htr₁, ← htr₂, ← htr₃]
  have htr_bob : tr_bob = (runMoves mid₃ (m₂.next tr₃)).1 := by
    rw [hmid₃_def, htr_bob_eq, hrun_ms₄₀, runMoves_append_fst]
  have hmid₃ : MovesFrom InvisibleNoEffect (m₂.next tr₃) mid₃ := by
    rw [hmid₃_def, movesFrom_append, ← hrun_ms₄₀]; exact ⟨hpost₂, hpre₃⟩
  have hrun_ms₄₃ : runTraceMoves r ms₄₃ = (runMoves post₃ (m₃.next tr_bob)).1 := by
    rw [hms₄₃, xpl_runTrace_eq]
    simp only [List.append_assoc, runMoves_append_fst, runMoves_cons_fst₀, ← xpl_runTrace_eq r ms₄₀, ← htr_bob_eq]
  have htr₄ : tr₄ = (runMoves mid₄ (m₃.next tr_bob)).1 := by
    rw [htr₄_raw, hmid₄_def, hrun_ms₄₃, runMoves_append_fst]
  have hmid₄ : MovesFrom InvisibleNoEffect (m₃.next tr_bob) mid₄ := by
    rw [hmid₄_def, movesFrom_append, ← hrun_ms₄₃]; exact ⟨hpost₃, hpre₄⟩
  have htr₅_run : (runMoves (ms₄₃ ++ pre₄ ++ m₄ :: mid₅) (setupTrace r)).1 = tr₅ := by
    rw [htr₅, htr₄_raw, List.append_assoc, runMoves_append_fst, runMoves_append_fst, ← xpl_runTrace_eq r ms₄₃, runMoves_cons_fst₀]
  have hpq₅ : pq₅ = tr₅.length + 2 := by
    rw [← htr₅_run]; exact pq_eq_of_ownSaltsFrom_split (post := post₅) hown hms
  subst hpq₅
  obtain ⟨st₅, hat₅, hns₅_max⟩ := encrypt_state_of_lastSent_ne_none hls₅
  have hE₅ : (Move.encrypt me₅ sIdx₅ cl₅ (tr₅.length + 2) (some (e₅, c₅))).next tr₅ =
      encNextTr tr₅ me₅ sIdx₅ st₅ cl₅ (tr₅.length + 2) :=
    encrypt_next_eq_encNextTr_of_ownSalt hat₅ hns₅_max rfl
  have hsm₅ := CliCoinSplit.sendMatches_of_encVis_split hc5 (encrypt_lastSent_eq_some_encOut hat₅ hns₅_max rfl) hm₅_vis
  have hat_tr₄ : ∀ j : Nat, (tr₄.at? j : Option TRStEntry) =
      if j = (bobStartTr tr_bob b_bob a_bob w_bob).length - 1 then some (TRStE b_bob (bobFinalSt tr_bob a_bob w_bob))
      else if j = tr₃.length + 5 then some (TRStE r.alice (encSt tr₃ (encSt tr₂ stA₁ cl₁) cl₂))
      else if j = tr₂.length + 5 then some (TRStE r.alice (encSt tr₂ stA₁ cl₁))
      else if j = tr₁.length + 8 then some (TRStE r.alice stA₁) else none :=
    at?_trSt_tr4_of_chain w_bob htr₁ hstA₁ htr₂ htr₃ htr_bob htr₄ hm₀ hE₁ hE₂ hnext_bob hpre₀ hmid₁ hmid₂ hmid₃ hmid₄
  have hnot_tr₄ : (tr₄.at? sIdx₅ : Option TRStEntry) ≠ some (TRStE me₅ st₅) := by
    intro htr₄_at; rw [hat_tr₄ sIdx₅] at htr₄_at
    have hcases : st₅ = bobFinalSt tr_bob a_bob w_bob ∨ st₅ = encSt tr₃ (encSt tr₂ stA₁ cl₁) cl₂ ∨ st₅ = encSt tr₂ stA₁ cl₁ ∨ st₅ = stA₁ := by
      split at htr₄_at
      · injection htr₄_at with he; injection he with he'; injection he' with _ hst; exact .inl hst.symm
      · split at htr₄_at
        · injection htr₄_at with he; injection he with he'; injection he' with _ hst; exact .inr (.inl hst.symm)
        · split at htr₄_at
          · injection htr₄_at with he; injection he with he'; injection he' with _ hst; exact .inr (.inr (.inl hst.symm))
          · split at htr₄_at
            · injection htr₄_at with he; injection he with he'; injection he' with _ hst; exact .inr (.inr (.inr hst.symm))
            · cases htr₄_at
    exact not_tr4_state_for_call5' w_bob hstA₁ hsm₁ hγ_rng41 hcases hsm₅
  have hneff : ¬ NoSessionEffect tr₄ m₄ := by
    intro heff; apply hnot_tr₄
    rw [← hat₅, htr₅, at?_trSt_of_movesFrom_invisibleNoEffect hmid₅, at?_trSt_of_noSessionEffect heff]
  obtain ⟨a₄, b₄, idS₄, regB₄, hb₄, sh₄, rfl, _, hdone₄, hm₄_vis⟩ := CompPrefixInvStruct.invert_ini_move_of_not_noSessionEffect hs₄ ha₄ hm₄ rs4_length rs4_kind hneff
  have htr₄_run : tr₄ = runTraceMoves r (ms₄₃ ++ pre₄) := by
    rw [htr₄_raw, ← CompPrefixInvStruct.runTrace_append r ms₄₃ pre₄]
  have ⟨_, hns_pre₄, hreach_pre₄, hnb_pre₄, hnoleak_pre₄⟩ := Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.NoFull.prefix_clean_hyps_of_matchedPrefix
      (ms₁ := ms₄₃ ++ pre₄)
      (ms₂ := Move.aliceStart a₄ b₄ idS₄ regB₄ hb₄ sh₄ :: mid₅ ++ Move.encrypt me₅ sIdx₅ cl₅ (tr₅.length + 2) (some (e₅, c₅)) :: post₅) hmp hnb
      (split81_no_leak hc1 hc2 hc5)
      (by rw [hms]; simp only [List.append_assoc, List.cons_append])
  have hms_all : ms = pre₀ ++ m₀ :: mid₁ ++ m₁ :: mid₂ ++ m₂ :: mid₃ ++ m₃ :: mid₄ ++ Move.aliceStart a₄ b₄ idS₄ regB₄ hb₄ sh₄ :: mid₅ ++ Move.encrypt me₅ sIdx₅ cl₅ (tr₅.length + 2) (some (e₅, c₅)) :: post₅ := by
    rw [hms, hms₄₃, hms₄₀, hmid₃_def, hmid₄_def]; simp only [List.append_assoc, List.cons_append]
  have hms_P₄ : ms = (pre₀ ++ (m₀ :: (mid₁ ++ (m₁ :: (mid₂ ++ (m₂ :: (mid₃ ++ (m₃ :: mid₄)))))))) ++ (Move.aliceStart a₄ b₄ idS₄ regB₄ hb₄ sh₄ :: mid₅ ++ Move.encrypt me₅ sIdx₅ cl₅ (tr₅.length + 2) (some (e₅, c₅)) :: post₅) := by
    rw [hms_all]; simp only [List.append_assoc, List.cons_append]
  obtain ⟨hs_P₄, ha_P₄⟩ := prefix_hyps_of_modelRun hmp.2.1 hms_P₄
  have hpq4 : ∀ j : Nat, (tr₄.at? j : Option PQXDHStEntry) = ((setupTrace r).at? j : Option PQXDHStEntry) := at?_pqSt_tr4_of_chain w_bob hs_P₄ ha_P₄ htr₁ htr₂ htr₃ htr_bob htr₄ hm₀ hE₁ hE₂ hnext_bob hpre₀ hmid₁ hmid₂ hmid₃ hmid₄
  obtain ⟨rfl, rfl, _, _, ikA₄, hid₄, hnext₄⟩ := pia_bundle_inv_of_reachable hNe htr₄_run hns_pre₄ hreach_pre₄ hnoleak_pre₄ hnb_pre₄ hpq4 hdone₄ hm₄_vis wireAt43_byte4
  have hat_tr₅ : (tr₅.at? sIdx₅ : Option TRStEntry) =
      if sIdx₅ = tr₄.length + 8 then some (TRStE a₄ (iniAliceStartState tr₄ r.bob (iniAliceOut tr₄ ikA₄ (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)))
      else (tr₄.at? sIdx₅ : Option TRStEntry) := by
    rw [htr₅, at?_trSt_of_movesFrom_invisibleNoEffect hmid₅, hnext₄, at?_trSt_iniAliceStartTr]
  have hsIdx₅_pin : sIdx₅ = tr₄.length + 8 ∧ me₅ = a₄ ∧ st₅ = iniAliceStartState tr₄ r.bob (iniAliceOut tr₄ ikA₄ (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none) := by
    rw [hat₅] at hat_tr₅
    split at hat_tr₅ <;> rename_i hsIdx_eq
    · injection hat_tr₅ with he; injection he with he'; injection he' with hme hst; exact ⟨hsIdx_eq, hme, hst⟩
    · exact absurd hat_tr₅.symm hnot_tr₄
  rcases hsIdx₅_pin with ⟨rfl, rfl, rfl⟩
  rcases hid₄ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  swap
  · exfalso
    obtain ⟨q₅, hq₅⟩ := sendAt80_parses
    obtain ⟨ek', ct', hL, -⟩ := CompRX0Mem.sendMatches_append_inv hsm₅ sendAt80_len hq₅
    rw [hL] at hsm₅
    have hs1 : compSecretIdx (clamp (secretBytes r 1)) = some ⟨4, by decide⟩ := by
      rw [hsb1]; exact idx1_bobId_secretIdx
    have hs2 : compSecretIdx (clamp (secretBytes r 2)) = some ⟨3, by decide⟩ := by
      rw [hsb2]; exact idx1_spk_secretIdx
    exact CompRX0Bytes.not_sendMatches_bobSelf hNe hEq hc hs1 hs2 (sendAt 80) sendAt80_hasTag4 tr₄ tr₅ r.bob _ _ ek' ct' cl₅ _ hsm₅
  obtain ⟨o₂, ho₂⟩ : ∃ o₂, o₂ = aliceOut tr₄ (setupSecret r 0) (setupPublic r 2)
      (setupPublic r 4) (setupPublic r 6) none := ⟨_, rfl⟩
  obtain ⟨stA₂, hstA₂⟩ : ∃ stA₂, stA₂ = aliceStartState tr₄ r.bob o₂ := ⟨_, rfl⟩
  have hnext₄' : (Move.aliceStart r.alice r.bob 4 6 hb₄ sh₄).next tr₄ =
      aliceStartTrOfOut tr₄ r.alice r.bob o₂ := by rw [← a_tr_eq, ho₂, ← a_out_eq]; exact hnext₄
  have hstA₂_eq : iniAliceStartState tr₄ r.bob (iniAliceOut tr₄ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none) = stA₂ := by
    rw [a_st_eq, a_out_eq, ← ho₂, ← hstA₂]
  rw [hstA₂_eq] at hE₅ hsm₅
  have hle_m₄_tr₅ : (Move.aliceStart r.alice r.bob 4 6 hb₄ sh₄).next tr₄ ≤ tr₅ := by
    rw [htr₅]; exact CompPrefixInvEnc.runMoves_le mid₅ _
  have hek₂ : NetMsgAt o₂.ek (tr₄.length + 3) tr₅ := by
    refine NetMsgAt.mono hle_m₄_tr₅ ?_
    rw [hnext₄', ← a_tr_eq]
    exact netMsgAt_ek_iniAliceStartTr tr₄ r.alice r.bob o₂
  have hct₂ : NetMsgAt o₂.ct (tr₄.length + 4) tr₅ := by
    refine NetMsgAt.mono hle_m₄_tr₅ ?_
    rw [hnext₄', ← a_tr_eq]
    exact netMsgAt_ct_iniAliceStartTr tr₄ r.alice r.bob o₂
  exact ⟨pre₀, mid₁, mid₂, mid₃, mid₄, mid₅, post₅, hb₀, hb₄, sh₀, sh₄, cl₁, e₁, c₁, cl₂, e₂, c₂, cl₅, e₅, c₅, b_bob, a_bob, kh, regIdxA, mh, pqIdx, spqrMsgIdx, sh_bob, tr₁, tr₂, tr₃, tr_bob, tr₄, tr₅, w_bob, o₁, o₂, stA₁, stA₂, htr₁, ho₁, hstA₁, htr₂, htr₃, htr_bob, htr₄, ho₂, hstA₂, htr₅, hms_all, hm₀, hE₁, hE₂, hnext_bob, hnext₄', hE₅, hpre₀, hmid₁, hmid₂, hmid₃, hmid₄, hmid₅, hpost₅, hek₁, hct₁, hek₂, hct₂, hvis₀, hm₄_vis, hsm₁, hsm₂, hsm₅⟩
end Symbolic.BugInjection.Proofs.Common443.WsIdx1Decomp81Core
