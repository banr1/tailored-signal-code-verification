/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.MacGuardGen
public import Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.BobDone
public import Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.Wire80
public import Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse

@[expose] public section
set_option autoImplicit false
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.NoFull
open CryptoProofLib.Refinement (ExternInterpretation)
open DY
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (MachineEvent)
open DY.Libsignal.Composed DY.Libsignal.Composed.Refinement
open DY.Libsignal.PQXDH (PQXDHEvent)
open DY.Libsignal.TripleRatchet (TREvent)
open Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED.CompInv Symbolic.BugInjection Symbolic.BugInjection.Proofs.Common443 Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1 Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.TraceFacts Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.Wire80 Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.MacGuardGen
open Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse (getEventAt_eq_at? eventLoggedAt_eq_at?)
theorem trace_no_leak : ∀ e ∈ trace, eventKind e ≠ .leak := by decide
theorem prefix_clean_hyps_of_matchedPrefix {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {ms ms₁ ms₂ : List Move} {τ : List MachineEvent} (hmp : Swarm.CREF.MatchedPrefix i r S g ms τ) (hnb : CompSetupSecrecy.NoBrk r ms) (hτ : ∀ e ∈ τ, eventKind e ≠ .leak) (hms : ms = ms₁ ++ ms₂) : r.alice ≠ r.bob ∧ (∀ m ∈ ms₁, m.isSetup = false) ∧ (runTraceMoves r ms₁).Reachable DY.Libsignal.Composed.reachability ∧ CompSetupSecrecy.NoBrk r ms₁ ∧ (∀ v ∈ runVis r ms₁, v.kind ≠ .leak) := by
  have ⟨hns, _, hnoleak⟩ := CompSetupSecrecy.crit_hyps_of_matchedPrefix_legacy hmp hτ
  refine ⟨CompSetupSecrecy.alice_ne_bob_of_modelRun hmp.2.1, fun m hm => hns m (hms ▸ List.mem_append_left _ hm),
    Swarm.CREF.matchedPrefix6_prefix_reachable hmp ms₁ ms₂ hms,
    CompSetupSecrecy.noBrk_of_le (by rw [hms, CompPrefixInvStruct.runTrace_append]; exact Swarm.CREF.runMoves_le _ _) hnb,
    fun v hv => hnoleak v ?_⟩
  have hrv : runVis r (ms₁ ++ ms₂) = runVis r ms₁ ++ (runMoves ms₂ (runTraceMoves r ms₁)).2 := by
    change (runMoves (r.setupMove :: (ms₁ ++ ms₂)) Trace.nil).2 = _
    rw [← List.cons_append, CompPrefixInvStruct.runMoves_append_snd]; rfl
  rw [hms, hrv]; exact List.mem_append_left _ hv
theorem bobStartOk_of_rpk_forall2 {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {tr : ExecTrace} {b a : Participant} {kh : DY.Libsignal.PQXDH.BobKeyHandles} {regA : Nat} {mh : DY.Libsignal.PQXDH.PreKeyMsgHandles} {pqIdx : Nat} {spqrMsgIdx : UInt32} {shown : Nat} {b_wire b_rng b_pt : HwBytes} {p : PreKeyFields} (hp : parsePreKeyWire b_wire = some p) (hm : List.Forall₂ (EventMatchesEntry i r S g) [.recv b_wire, .rng b_rng, .accept b_pt] ((Move.bobStart b a kh regA mh pqIdx spqrMsgIdx shown).vis tr)) : ∃ w : CompSetupSecrecy.BobStartOk tr b a kh regA mh pqIdx spqrMsgIdx, ecKey (gamma i S g w.ek) = p.baseKey.take 33 ∧ gamma i S g w.raw = p.message := by
  have hnoleak_vis : ∀ v ∈ (Move.bobStart b a kh regA mh pqIdx spqrMsgIdx shown).vis tr, v.kind ≠ .leak :=
    CompSetupSecrecy.crit_noleak_of_forall2 (by intro e he; simp at he; rcases he with rfl | rfl | rfl <;> nofun) hm
  generalize hvis : (Move.bobStart b a kh regA mh pqIdx spqrMsgIdx shown).vis tr = vis at hm hnoleak_vis
  rcases hm with _ | ⟨hm0, _ | ⟨_, _ | ⟨hm2, _ | _⟩⟩⟩; rename_i v₀ v₁ v₂
  have hmem2 : v₂ ∈ (Move.bobStart b a kh regA mh pqIdx spqrMsgIdx shown).vis tr := by rw [hvis]; simp
  obtain ⟨w⟩ := CompSetupSecrecy.bobStart_accept_ok hmem2 hm2.1.symm; obtain ⟨p', hp', hbk, _, hmsg, _⟩ := w.preKeyRecvMatches_of_vis hvis hnoleak_vis hm0; change parsePreKeyWire b_wire = some p' at hp'; rw [hp] at hp'; cases hp'; exact ⟨w, hbk.symm, hmsg.symm⟩
theorem matchedPrefix_ini_split {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {τ_pre blk : List MachineEvent} {ks : List Kind} {ms : List Move} (hmap : blk.map eventKind = .recv :: ks) (hks : ∀ k ∈ ks, k = .rng) (hmp : Swarm.CREF.MatchedPrefix i r S g ms (τ_pre ++ blk)) : ∃ ms₀ δ bun rs, ms = ms₀ ++ δ ∧ Swarm.CREF.MatchedPrefix i r S g ms₀ τ_pre ∧ XplBlock6 i r S g ms₀ δ τ_pre (.recv bun :: rs) ∧ ∀ e ∈ rs, eventKind e = .rng := by
  obtain ⟨bun, rs, rfl, hrs⟩ := iniShape_of_map_eventKind hmap hks
  obtain ⟨ms₀, δ, rfl, hmp₀, hfor⟩ := matchedPrefix6_split hmp (by intro e he; simp at he; subst he; exact Or.inl rfl)
    (matchedPrefix6_prefix_reachable hmp)
  exact ⟨ms₀, δ, bun, rs, rfl, hmp₀, ⟨hmp₀, hmp.2.1, hfor⟩, hrs⟩
theorem matchedPrefix_send_split {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {τ_pre blk : List MachineEvent} {ks : List Kind} {ms : List Move} (hmap : blk.map eventKind = .pt :: ks) (hks : ∀ k ∈ ks, k = .rng ∨ k = .send) (hmp : Swarm.CREF.MatchedPrefix i r S g ms (τ_pre ++ blk)) : ∃ ms₀ δ b_pt tail, ms = ms₀ ++ δ ∧ Swarm.CREF.MatchedPrefix i r S g ms₀ τ_pre ∧ XplBlock6 i r S g ms₀ δ τ_pre (.pt b_pt :: tail) ∧ ∀ e ∈ tail, eventKind e = .rng ∨ eventKind e = .send := by
  obtain ⟨b_pt, tail, rfl, htail⟩ := sendShape_of_map_eventKind hmap hks
  obtain ⟨ms₀, δ, rfl, hmp₀, hfor⟩ := matchedPrefix6_split hmp (by intro e he; simp at he; subst he; exact Or.inr rfl)
    (matchedPrefix6_prefix_reachable hmp)
  exact ⟨ms₀, δ, b_pt, tail, rfl, hmp₀, ⟨hmp₀, hmp.2.1, hfor⟩, htail⟩
theorem take43_allAliceDone_ek1 {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {ms : List Move} (hnb : CompSetupSecrecy.NoBrk r ms) (hmp : Swarm.CREF.MatchedPrefix i r S g ms (trace.take 43)) : AllAliceDone (fun ek => ecKey (gamma i S g ek) = ecKey ek1PubKey) (runTraceMoves r ms) := by
  have hmp43 := hmp; rw [take43_eq] at hmp; obtain ⟨b_rng, b_pt, hseg⟩ := seg40_eq; rw [hseg] at hmp; obtain ⟨p, hp⟩ := wireAt40_parses; have hp_bk : p.baseKey.take 33 = ecKey ek1PubKey := baseKey_of_map wireAt40_baseKey hp
  obtain ⟨ms₄₀, pre, post, b, a, kh, regA, mh, pqIdx, spqrMsgIdx, shown, hms, hmp₄₀, _, hpre_inv, hpost_inv, _, hm⟩ := BobDone.matchedPrefix_rpk_bobStart_only i r S g (trace.take 40) (wireAt 40) b_rng b_pt ms p
      wireAt40_head? hp (fun _ hmp₀ => BobDone.take40_not_knownBaseKey hmp₀) hmp
  have h40 : ∃ ek₀, AllAliceDone (· = ek₀) (runTraceMoves r ms₄₀) := by
    rw [take40_eq] at hmp₄₀
    obtain ⟨ms₃₈, δ₂, _, tail₂, rfl, hmp₃₈, hB₂, htail₂⟩ := matchedPrefix_send_split seg38_kinds (fun _ hk => rng_send_of_mem_send hk) hmp₄₀
    rw [take38_eq] at hmp₃₈
    obtain ⟨ms₃₅, δ₁, _, tail₁, rfl, hmp₃₅, hB₁, htail₁⟩ := matchedPrefix_send_split seg35_kinds (fun _ hk => rng_send_of_mem_rng_send hk) hmp₃₈
    have hNe := CompSetupSecrecy.alice_ne_bob_of_modelRun hmp₃₅.2.1; rw [take35_eq] at hmp₃₅; obtain ⟨ms₀, δ₀, _, rs₀, rfl, hmp₀, hB₀, hrs₀⟩ := matchedPrefix_ini_split seg0_kinds (replicate_rng 34) hmp₃₅
    have hnil : AllAliceDone (fun _ => False) (runTraceMoves r ms₀) := by rw [xpl_runTrace_eq]; exact allAliceDone_of_movesFrom_invisible (BobDone.movesFrom_invisibleNoEffect_of_matchedPrefix_nil hmp₀) (allAliceDone_setupTrace hNe _)
    obtain ⟨ek₀, h₃₅⟩ := allAliceDone_xplBlock_ini hB₀ hrs₀ hnil; exact ⟨ek₀, allAliceDone_xplBlock_send hB₂ htail₂ (allAliceDone_xplBlock_send hB₁ htail₁ h₃₅)⟩
  obtain ⟨ek₀, h40⟩ := h40; have htr_eq : (runMoves pre (runTraceMoves r ms₄₀)).1 = runTraceMoves r (ms₄₀ ++ pre) := (CompPrefixInvStruct.runTrace_append r ms₄₀ pre).symm
  have htr_pre : AllAliceDone (· = ek₀) (runTraceMoves r (ms₄₀ ++ pre)) := htr_eq ▸ allAliceDone_of_movesFrom_invisible hpre_inv h40
  have ⟨hNe, hns, hreach, hnb_pre, hnoleak⟩ := prefix_clean_hyps_of_matchedPrefix (ms₁ := ms₄₀ ++ pre) (ms₂ := Move.bobStart b a kh regA mh pqIdx spqrMsgIdx shown :: post) hmp43 hnb
    (fun e he => trace_no_leak e (List.mem_of_mem_take he)) (by simp [hms, List.append_assoc])
  rw [htr_eq] at hm; obtain ⟨w, hbk, _⟩ := bobStartOk_of_rpk_forall2 hp hm; obtain ⟨_, _, a', b', spk', opk', _, _, _, hAlice, _⟩ := w.aliceMatch_and_ek_dhPk_of_no_leak hNe hns hreach hnoleak hnb_pre; have hek₀ : w.ek = ek₀ := htr_pre _ _ _ _ _ _ _ _ _ _ _ hAlice
  have htr_ek1 : AllAliceDone (fun ek => ecKey (gamma i S g ek) = ecKey ek1PubKey) (runMoves pre (runTraceMoves r ms₄₀)).1 :=
    fun a1 b1 ikA1 ikB1 spk1 pqpk1 opk1 e1 ct1 keys1 j1 hev1 => by
      dsimp only; rw [allAliceDone_of_movesFrom_invisible hpre_inv h40 a1 b1 ikA1 ikB1 spk1 pqpk1 opk1 e1 ct1 keys1 j1 hev1, ← hek₀, hbk, hp_bk]
  rw [hms, CompPrefixInvStruct.runTrace_append, CompPrefixInvStruct.runMoves_append_fst, runMoves_cons_fst]; exact allAliceDone_of_movesFrom_invisible hpost_inv (allAliceDone_bobStart b a kh regA mh pqIdx spqrMsgIdx shown htr_ek1)
theorem noFull : SpecTop.NoFullMatchWS := by
  intro r S g ms _ hnb hmp0; have hmp := Swarm.CREF.MatchedPrefix.of_composed hmp0; obtain ⟨p₈₁, hp₈₁⟩ := wireAt81_parses; obtain ⟨b_rng, b_pt, hseg⟩ := seg81_eq
  have hmp' : Swarm.CREF.MatchedPrefix SpecTop.compI0 r S g ms (trace.take 81 ++ [.recv (wireAt 81), .rng b_rng, .accept b_pt]) := by rw [← hseg, ← trace_eq]; exact hmp
  obtain ⟨ms₈₁, pre, post, b, a, kh, regIdxA, mh, pqIdx, spqrMsgIdx, shown, hms, hmp₈₁, _, hpre_inv, _, _, hm⟩ := BobDone.matchedPrefix_rpk_bobStart_only SpecTop.compI0 r S g (trace.take 81) (wireAt 81) b_rng b_pt ms p₈₁
      wireAt81_head? hp₈₁ (fun _ hmp₀ => BobDone.take81_not_knownBaseKey hmp₀ hp₈₁) hmp'
  have hmp₈₁' := hmp₈₁; rw [take81_eq] at hmp₈₁'; obtain ⟨pt₅, c₅, hseg₇₈⟩ := seg78_eq; rw [hseg₇₈] at hmp₈₁'
  obtain ⟨ms₇₈, δ₅, rfl, hmp₇₈, hfor₅⟩ := matchedPrefix6_split hmp₈₁'
    (by intro e he; simp at he; subst he; exact Or.inr rfl) (matchedPrefix6_prefix_reachable hmp₈₁')
  have hmp₇₈' := hmp₇₈; rw [take78_eq] at hmp₇₈'; obtain ⟨ms₄₃, δ₄, bun₄, rs₄, rfl, hmp₄₃, hB₄, hrs₄⟩ := matchedPrefix_ini_split seg43_kinds (replicate_rng 34) hmp₇₈'; obtain ⟨p₈₀, hp₈₀⟩ := sendAt80_parses; have hp₈₁_bk : p₈₁.baseKey.take 33 = ecKey ek2PubKey := baseKey_of_map wireAt81_baseKey hp₈₁
  have hSent₈₁ : AllSentNet (runTraceMoves r ms₄₃).length (fun raw => gamma SpecTop.compI0 S g raw = p₈₀.message)
      (runTraceMoves r ((ms₄₃ ++ δ₄) ++ δ₅)) :=
    allSentNet_xplBlock_send ⟨hmp₇₈, hmp₈₁.2.1, hfor₅⟩ sendAt80_head_ne_whisper sendAt80_length_lt
      hp₈₀ (allSentNet_xplBlock_ini hB₄ hrs₄ (allSentNet_self _ (runTraceMoves r ms₄₃))) (fun _ h => h)
  have hSent_pre := allSentNet_runMoves_of_movesFrom hpre_inv hSent₈₁; have htr_eq : (runMoves pre (runTraceMoves r ((ms₄₃ ++ δ₄) ++ δ₅))).1 = runTraceMoves r (((ms₄₃ ++ δ₄) ++ δ₅) ++ pre) := (CompPrefixInvStruct.runTrace_append r ((ms₄₃ ++ δ₄) ++ δ₅) pre).symm; rw [htr_eq] at hm hSent_pre; obtain ⟨w, hbk₈₁, hraw₈₁⟩ := bobStartOk_of_rpk_forall2 hp₈₁ hm
  have ⟨hNe, hns, hreach, hnb_pre, hnoleak⟩ := prefix_clean_hyps_of_matchedPrefix (ms₁ := ((ms₄₃ ++ δ₄) ++ δ₅) ++ pre) (ms₂ := Move.bobStart b a kh regIdxA mh pqIdx spqrMsgIdx shown :: post)
    hmp hnb trace_no_leak (by simp [hms, List.append_assoc])
  obtain ⟨t, me, peer, dhs, ns, m_pt, _, hsent_ev, hnet_raw, hAlice⟩ := MacGuardGen.BobStartOk.sentMac_of_no_leak hNe hns hreach hnb_pre hnoleak w
  by_cases hk : (runTraceMoves r ms₄₃).length ≤ t + 3
  · have hget_sent : (runTraceMoves r (((ms₄₃ ++ δ₄) ++ δ₅) ++ pre)).getEventAt TREvent (t + 3) = some (TREvent.Sent me peer dhs ns m_pt) := by
      rw [getEventAt_eq_at?]; rw [eventLoggedAt_eq_at?] at hsent_ev; rw [hsent_ev]
    obtain ⟨raw', _, hnet_raw', hp₈₀_raw'⟩ := hSent_pre (t + 3) _ hk hget_sent rfl
    have hraw_eq : w.raw = raw' := by
      unfold NetAt at hnet_raw hnet_raw'; rw [show t + 3 + 3 = t + 6 by omega, hnet_raw] at hnet_raw'; cases hnet_raw'; rfl
    have hmsg_eq : p₈₁.message = p₈₀.message := by rw [← hraw₈₁, hraw_eq, hp₈₀_raw']
    exact wireAt81_inner_ne_sendAt80_inner hp₈₁ hp₈₀ (congrArg (fun x => x.take (x.length - 8)) hmsg_eq)
  · obtain ⟨j, a', b', spk', opk', hjt, hAlice_ev⟩ := hAlice
    have hj₄₃ : j < (runTraceMoves r ms₄₃).length := by omega
    have hle₄₃ : runTraceMoves r ms₄₃ ≤ runTraceMoves r (((ms₄₃ ++ δ₄) ++ δ₅) ++ pre) := by rw [List.append_assoc, List.append_assoc, CompPrefixInvStruct.runTrace_append]; exact Swarm.CREF.runMoves_le _ _
    have hAlice₄₃_ev : (runTraceMoves r ms₄₃).EventLoggedAt (PQXDHEvent.AliceDone a' b' w.ikAPk (DiffieHellman.dhPk w.ikB) spk' (PQKem.kemPk w.pqsk) opk' w.ek w.ct w.keys) j := by
      rw [eventLoggedAt_eq_at?] at hAlice_ev ⊢; rwa [← CompSetupSecrecy.at?_eq_of_le_of_lt hle₄₃ hj₄₃]
    have hnb₄₃ : CompSetupSecrecy.NoBrk r ms₄₃ := CompSetupSecrecy.noBrk_of_le hle₄₃ hnb_pre
    have hek1 := take43_allAliceDone_ek1 hnb₄₃ hmp₄₃ a' b' _ _ spk' _ opk' w.ek w.ct w.keys j hAlice₄₃_ev; exact ek1_ne_ek2 (hek1.symm.trans (hbk₈₁.trans hp₈₁_bk))
end Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.NoFull
