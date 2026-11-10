/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.CompMemoInjGtDraws
public import Symbolic.BugInjection.Proofs.Common443.CompSetupSecrecy
public import Symbolic.BugInjection.Proofs.Common443.CompPrefixInvStruct
public import Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice
public import Symbolic.BugInjection.Proofs.Common443.CompPrefixInvBundle
public import Symbolic.BugInjection.Proofs.Common443.CompPrefixInvEnc

@[expose] public section
set_option autoImplicit false
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Common443.CompPrefixInvIni
open DY
open DY.Libsignal (HwBytes)
open DY.Libsignal.Composed DY.Libsignal.Composed.Refinement DY.Libsignal.HwEvents
open CryptoProofLib.Refinement (ExternInterpretation)
open Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.Swarm.COMPOSED.CompTrace Symbolic.BugInjection.Proofs.Common443.CompMemoInjGt
theorem storedSecrets_inv_of_no_setup {r : Records} {ms : List Move} (hwf : RecordsWF r) (hns : ∀ m ∈ ms, m.isSetup = false) (hreach : (runTraceMoves r ms).Reachable DY.Libsignal.Composed.reachability) : ∀ j : Nat, ∀ e : PQXDHStEntry, ((runTraceMoves r ms).at? j : Option PQXDHStEntry) = some e → e.st.state.sk = setupSecret r 0 ∨ e.st.state.sk = setupSecret r 1 ∨ e.st.state.sk = setupSecret r 2 ∨ e.st.state.sk = setupSecret r 4 ∨ (r.withOpk = true ∧ e.st.state.sk = randTerm 22 32) := by
  have hinv := Symbolic.Swarm.COMPOSED.CompInv.spqrInv_of_reachable (runTraceMoves r ms) hreach; intro j ⟨⟨part, kind, sk⟩⟩ hat; have hkind : Symbolic.Swarm.COMPOSED.CompInv.KindOK (runTraceMoves r ms) part { kind := kind, sk := sk } := hinv.stOK part { kind := kind, sk := sk } j hat; dsimp only [Symbolic.Swarm.COMPOSED.CompInv.KindOK] at hkind ⊢
  cases kind with
  | identity =>
    rcases CompSetupSecrecy.ikAt_cases_of_no_setup hwf.1 hns hkind with ⟨_, hsk, _⟩ | ⟨_, hsk, _⟩
    · exact .inl hsk
    · exact .inr (.inl hsk)
  | signedPrekey =>
    obtain ⟨_, hsk, _⟩ := CompSetupSecrecy.spkAt_eq_of_no_setup hwf.1 hns hkind; exact .inr (.inr (.inl hsk))
  | pqPrekey =>
    obtain ⟨_, hsk, _⟩ := CompSetupSecrecy.pqAt_eq_of_no_setup hwf.1 hns hkind; exact .inr (.inr (.inr (.inl hsk)))
  | oneTimePrekey =>
    obtain ⟨t, rfl, _, hev⟩ := hkind; have h0 := CompSetupSecrecy.noNewNonMovePQEv_runTrace r ms hns _ (t + 1) rfl hev
    rcases CompSetupSecrecy.setupTrace_eventLoggedAt_cases hwf.1 h0 with
      ⟨_, heq⟩ | ⟨_, heq⟩ | ⟨_, heq⟩ | ⟨_, heq⟩ | ⟨hopk, ht, _⟩
    · cases heq
    · cases heq
    · cases heq
    · cases heq
    · have ht22 : t = 22 := by omega
      subst ht22; exact .inr (.inr (.inr (.inr ⟨hopk, rfl⟩)))
theorem movesAnchored_append_left' : ∀ (ms₁ ms₂ : List Move) (tr : ExecTrace), MovesAnchored (ms₁ ++ ms₂) tr → MovesAnchored ms₁ tr
  | [], _, _, _ => trivial
  | m :: ms₁, ms₂, tr, ⟨hm, hrest⟩ =>
    ⟨hm, movesAnchored_append_left' ms₁ ms₂ (m.next tr) hrest⟩
theorem runMoves_cons_fst' (m : Move) (ms : List Move) (tr : ExecTrace) : (runMoves (m :: ms) tr).1 = (runMoves ms (m.next tr)).1 := rfl
attribute [local irreducible] setupPublic setupSecret
theorem iniPrefixStateSecretsInv_of_matchedPrefix_ini {r : Records} {S : Sem} {who : List Participant} {g : Ghost} {ms : List Move} {bun : HwBytes} {rs : List MachineEvent} (hwf : RecordsWF r) (hnb : CompSetupSecrecy.NoBrk r ms) (hmp : MatchedPrefix compI0 r S who g ms (.recv bun :: rs)) (hrs_len : rs.length = 34) (hrs_kind : ∀ e ∈ rs, eventKind e = .rng) (hbun4 : bun[4]? ≠ some 1#8) : IniPrefixStateSecretsInv r S g ms bun rs := by
  have hmp_old : Symbolic.Swarm.CREF.MatchedPrefix compI0 r S g ms (.recv bun :: rs) := Symbolic.Swarm.CREF.MatchedPrefix.of_composed hmp; have hNe : r.alice ≠ r.bob := hwf.1
  have hreach_all : (runTraceMoves r ms).Reachable DY.Libsignal.Composed.reachability :=
    CompPrefixInvStruct.matchedPrefix6_prefix_reachable hmp_old ms [] (by simp)
  refine ⟨storedSecrets_inv_of_no_setup hwf hmp_old.2.1.2.1 hreach_all, ?_⟩; intro ls hls; let blk₁ : List MachineEvent := .recv bun :: rs;
  have hhead₁ : ∀ e ∈ blk₁.head?, eventKind e = .recv ∨ eventKind e = .pt := by intro e he; simp [blk₁] at he; subst he; exact Or.inl rfl
  have hmp₁' : Symbolic.Swarm.CREF.MatchedPrefix compI0 r S g ms ([] ++ blk₁) := by simpa using hmp_old
  obtain ⟨ms₀, δ₁, hms₁, hmp₀, hfor₁⟩ := Symbolic.Swarm.CREF.matchedPrefix6_split hmp₁' hhead₁ (CompPrefixInvStruct.matchedPrefix6_prefix_reachable hmp₁'); have hB₁ : Symbolic.Swarm.CREF.XplBlock6 compI0 r S g ms₀ δ₁ [] blk₁ := ⟨hmp₀, hms₁ ▸ hmp_old.2.1, hfor₁⟩
  have hne₁ : blk₁ ≠ [] := by simp [blk₁]
  have htail₁ : ∀ e ∈ blk₁.tail, eventKind e ≠ .recv ∧ eventKind e ≠ .pt ∧ eventKind e ≠ .leak := by intro e he; rw [hrs_kind e he]; decide
  obtain ⟨pre₁, m₀, post₁, rfl, hpre₁, ⟨hs₀, ha₀, hm₀⟩, hpost₁⟩ := Symbolic.Swarm.CREF.xpl6_oneMove hB₁ hhead₁ hne₁ htail₁; let pre := ms₀ ++ pre₁; have htr₁_eq : (runMoves pre₁ (runTraceMoves r ms₀)).1 = (runMoves pre (setupTrace r)).1 := (by dsimp [pre]; rw [CompPrefixInvStruct.runMoves_append_fst, ← Symbolic.Swarm.CREF.xpl_runTrace_eq]); rw [htr₁_eq] at ha₀ hm₀ hpost₁; have hpre : Symbolic.Swarm.CREF.MovesFrom Symbolic.Swarm.CREF.InvisibleNoEffect (setupTrace r) pre := (by rw [Symbolic.Swarm.CREF.movesFrom_append, ← Symbolic.Swarm.CREF.xpl_runTrace_eq]; exact ⟨CompPrefixInvStruct.movesFrom_invisibleNoEffect_of_matchedPrefix_nil hmp₀, hpre₁⟩)
  have hms_eq : ms = pre ++ m₀ :: post₁ := by simp [hms₁, pre, List.append_assoc]
  have hrun_ms : runTraceMoves r ms = (runMoves post₁ (m₀.next (runMoves pre (setupTrace r)).1)).1 := (by rw [hms_eq, Symbolic.Swarm.CREF.xpl_runTrace_eq, CompPrefixInvStruct.runMoves_append_fst, runMoves_cons_fst'])
  have hno₁ : CompPrefixInvStruct.NoTRState (runMoves pre (setupTrace r)).1 := CompPrefixInvStruct.noTRState_of_movesFrom_invisibleNoEffect
      (CompPrefixInvStruct.noTRState_setupTrace r) hpre
  by_cases heff : Symbolic.Swarm.CREF.NoSessionEffect (runMoves pre (setupTrace r)).1 m₀
  · exfalso; have hno_m₀ : CompPrefixInvStruct.NoTRState (m₀.next (runMoves pre (setupTrace r)).1) := CompPrefixInvStruct.noTRState_of_noSessionEffect hno₁ heff; have hno_ms : CompPrefixInvStruct.NoTRState (runTraceMoves r ms) := (by rw [hrun_ms]; exact CompPrefixInvStruct.noTRState_of_movesFrom_invisibleNoEffect hno_m₀ hpost₁); unfold storedStates newIndices DY.ExecTrace.getLocalStateAt at hls; simp only [List.mem_filterMap, List.mem_range'_1, Option.map_eq_some_iff] at hls; obtain ⟨j, _, ⟨ls'⟩, hat, _⟩ := hls; rw [hno_ms j] at hat; cases hat
  · obtain ⟨a, b, idS, regB, hb, shown, rfl, _, hdone, hm₀_vis⟩ := CompPrefixInvStruct.invert_ini_move_of_not_noSessionEffect hs₀ ha₀ hm₀ hrs_len hrs_kind heff; have hreach₁ : (runMoves pre (setupTrace r)).1.Reachable DY.Libsignal.Composed.reachability := (by rw [← Symbolic.Swarm.CREF.xpl_runTrace_eq]; exact CompPrefixInvStruct.matchedPrefix6_prefix_reachable hmp_old pre (.aliceStart a b idS regB hb shown :: post₁) hms_eq); have hnb_pre : CompSetupSecrecy.NoBrk r pre := CompSetupSecrecy.noBrk_of_le (by rw [hms_eq, Symbolic.Swarm.CREF.xpl_runTrace_eq (ms := pre ++ _), CompPrefixInvStruct.runMoves_append_fst (ms₁ := pre), ← Symbolic.Swarm.CREF.xpl_runTrace_eq]; exact CompPrefixInvEnc.runMoves_le _ _) hnb; have hs_pre : ∀ m ∈ pre, m.isSetup = false := (by intro m hm; exact hmp_old.2.1.2.1 m (by rw [hms_eq]; exact List.mem_append_left _ hm)); have ha_pre : MovesAnchored pre (setupTrace r) := (by have ha_all := hmp_old.2.1.2.2.1.2.1; rw [hms_eq] at ha_all; exact movesAnchored_append_left' pre _ (setupTrace r) ha_all); obtain ⟨rfl, rfl, _, _, ikA, _, _, hid, _, _, _, _, _, _, _, hnext⟩ := CompPrefixInvBundle.pia_bundle_inv hNe hnb_pre hs_pre ha_pre hpre hreach₁ hdone hm₀_vis hbun4; generalize (runMoves pre (setupTrace r)).1 = tr₁ at hrun_ms hno₁ hpost₁ hm₀_vis hnext; let o := CompPrefixInvAlice.iniAliceOut tr₁ ikA (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none;
    have hnext' : (Move.aliceStart a r.bob idS 6 hb shown).next tr₁ =
        CompPrefixInvAlice.iniAliceStartTr tr₁ a r.bob o := hnext
    unfold storedStates newIndices DY.ExecTrace.getLocalStateAt at hls; simp only [List.mem_filterMap, List.mem_range'_1, Option.map_eq_some_iff] at hls; obtain ⟨j, _, ⟨ls'⟩, hat, rfl⟩ := hls; rw [hrun_ms, CompPrefixInvEnc.at?_trSt_of_movesFrom_invisibleNoEffect hpost₁ j, hnext', CompPrefixInvAlice.at?_trSt_iniAliceStartTr_of_noTRState hno₁ a r.bob o j] at hat
    split_ifs at hat with hj
    injection hat with hls_eq
    have hls_eq' : ls' = ⟨a, CompPrefixInvAlice.iniAliceStartState tr₁ r.bob o⟩ :=
      congrArg (fun e : Symbolic.Swarm.COMPOSED.CompTrace.TRStEntry => e.st) hls_eq.symm
    subst hls_eq'; rw [hnext'] at hm₀_vis
    have hid' : ikA = setupSecret r 0 ∨ ikA = setupSecret r 1 := by
      rcases hid with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩
      · exact .inl rfl
      · exact .inr rfl
    exact ⟨tr₁, a, ikA, hb, hid', hm₀_vis, rfl⟩
end Symbolic.BugInjection.Proofs.Common443.CompPrefixInvIni
