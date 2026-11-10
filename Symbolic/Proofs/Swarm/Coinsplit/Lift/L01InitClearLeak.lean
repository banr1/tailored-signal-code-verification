/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.Coinsplit.Lift.Defs
import DY.Actions.ProtocolEvent
import Symbolic.Proofs.Swarm.CREF.Cli.World.InitModelPure
import Symbolic.Proofs.Swarm.CREF.Cli.World.InitPure
import Symbolic.Proofs.Swarm.CREF.Cli.World.LeakModelPure
import Symbolic.Proofs.Swarm.CREF.Cli.World.LeakPure
import Symbolic.Proofs.Swarm.CREF.Cli.World.RelCliPure
import Symbolic.Proofs.Swarm.CREF.Cli.World.TurnPure
import Symbolic.Proofs.Swarm.CREF.Cli.World.XplTransferPure
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.DYBridge.DY.Actions.ProtocolEvent

/-!
# Initialization, Session Clear, and Leak Stepping for `CliLiveAtCli`

Proves `init_clear_leak : GoodExit0CutSpec → InitClearLeakSpec`: base initialization (`σ_acc = []`),
`clearSession` framing, and inductive `.leak` stepping for `CliLiveAtCli`.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.Coinsplit.Lift.L01

cref_open
open CryptoProofLib.Refinement (ExternInterpretation)
open _root_.DY.Libsignal.HwEvents (MachineEvent)
open _root_.DY.Libsignal.Composed.Refinement
open _root_.DY.Libsignal.Composed.Refinement.Cli
open Symbolic.Swarm.CREF
open Symbolic.Swarm.CREF.CliPure
open Symbolic.Swarm.Coinsplit.S1 (NoAdjRng)
open Symbolic.Swarm.Coinsplit.Lift

private theorem coinSplit_eq_of_all_nonRng {ys τ : List MachineEvent}
    (hno : ∀ e ∈ ys, eventKind e ≠ .rng) (hcs : CoinSplit ys τ) :
    τ = ys := by
  induction ys generalizing τ with
  | nil =>
    cases hcs
    rfl
  | cons y ys' ih =>
    have hy : eventKind y ≠ .rng := hno y (List.mem_cons_self ..)
    obtain ⟨τ', rfl, hcs'⟩ := (S1.coinSplit_cons_nonRng_iff hy).mp hcs
    rw [ih (fun e he => hno e (List.mem_cons_of_mem _ he)) hcs']

private theorem coinSplit_append_of_all_nonRng {xs ys τ : List MachineEvent}
    (hno : ∀ e ∈ ys, eventKind e ≠ .rng)
    (hcs : CoinSplit (xs ++ ys) τ) :
    ∃ τ_pre, τ = τ_pre ++ ys ∧ CoinSplit xs τ_pre := by
  induction xs generalizing τ with
  | nil =>
    exact ⟨[], by simpa using coinSplit_eq_of_all_nonRng hno hcs, .nil⟩
  | cons x xs' ih =>
    by_cases hx : eventKind x = .rng
    · cases x <;> try simp [eventKind] at hx
      rename_i coins
      obtain ⟨pieces, τ₁, hne, hpref, rfl, hcs₁⟩ := S1.coinSplit_cons_rng_iff.mp hcs
      obtain ⟨τ_pre, rfl, hcs_pre⟩ := ih hcs₁
      exact ⟨pieces.map MachineEvent.rng ++ τ_pre,
        (List.append_assoc _ _ _).symm,
        .split hne hpref hcs_pre⟩
    · obtain ⟨τ₁, rfl, hcs₁⟩ := (S1.coinSplit_cons_nonRng_iff hx).mp hcs
      obtain ⟨τ_pre, rfl, hcs_pre⟩ := ih hcs₁
      exact ⟨x :: τ_pre, rfl, (S1.coinSplit_cons_nonRng_iff hx).mpr ⟨τ_pre, rfl, hcs_pre⟩⟩

private theorem explainsCli_nil {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool} {g : Ghost}
    (hc : Clean interp r S who ok g [] []) :
    ExplainsCli interp r S who ok [] [] g [] := by
  have hofc : OutcomeFaithfulCli r ok [] := ⟨hc.1.2, fun _ _ hi => nomatch hi⟩
  unfold ExplainsCli
  refine ⟨CoinSplit.nil, hc.matched, ?_⟩
  first
  | exact hofc
  | exact ⟨hofc, fun _ _ hi => nomatch hi⟩

private theorem outcomeFaithfulCli_prefix {r : ProtocolSetup} {ok : Nat → Bool}
    {ms_pre δ : List Move}
    (hof_pre : OutcomeFaithful r ok ms_pre)
    (hofc : OutcomeFaithfulCli r ok (ms_pre ++ δ)) :
    OutcomeFaithfulCli r ok ms_pre := by
  refine ⟨hof_pre, fun i m hi => ?_⟩
  have hlt : i < ms_pre.length := (List.getElem?_eq_some_iff.mp hi).1
  have hget : (ms_pre ++ δ)[i]? = some m := by
    rw [List.getElem?_append_left hlt]; exact hi
  have htake : (ms_pre ++ δ).take i = ms_pre.take i :=
    List.take_append_of_le_length (Nat.le_of_lt hlt)
  have h := hofc.2 i m hget
  dsimp only at h ⊢
  rwa [htake] at h

private theorem explainsCli_prefix {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool}
    {σ_acc leaks τ_pre : List MachineEvent} {g : Ghost} {ms_pre δ : List Move}
    (hcs_pre : CoinSplit σ_acc τ_pre)
    (hmp_pre : MatchedPrefix interp r S who g ms_pre τ_pre)
    (hof_pre : OutcomeFaithful r ok ms_pre)
    (hex : ExplainsCli interp r S who ok (σ_acc ++ leaks) (τ_pre ++ leaks) g (ms_pre ++ δ)) :
    ExplainsCli interp r S who ok σ_acc τ_pre g ms_pre := by
  unfold ExplainsCli at hex ⊢
  rcases hex with ⟨_, _, hrest⟩
  refine ⟨hcs_pre, hmp_pre, ?_⟩
  first
  | exact outcomeFaithfulCli_prefix hof_pre hrest
  | rcases hrest with ⟨hofc, hrng⟩
    refine ⟨outcomeFaithfulCli_prefix hof_pre hofc, fun i m hi => ?_⟩
    have hlt : i < ms_pre.length := (List.getElem?_eq_some_iff.mp hi).1
    have hget : (ms_pre ++ δ)[i]? = some m := by
      rw [List.getElem?_append_left hlt]; exact hi
    have htake : (ms_pre ++ δ).take i = ms_pre.take i :=
      List.take_append_of_le_length (Nat.le_of_lt hlt)
    have h := hrng i m hget
    dsimp only at h ⊢
    rwa [htake] at h

private def zAnyPure : TR.PureTRSlots :=
  { canon := fun _ _ => True, recvSim := fun _ _ => True, tok := fun _ => True }

private theorem find?_eq_some_of_mem_nodup {α β : Type} (f : α → β) {l : List α}
    (hnd : (l.map f).Nodup) {x : α} (hx : x ∈ l) (p : α → Bool)
    (hpx : p x = true) (hpf : ∀ y, p y = true → f y = f x) :
    l.find? p = some x := by
  induction l with
  | nil => cases hx
  | cons a xs ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    rcases List.mem_cons.mp hx with rfl | hx'
    · simp [List.find?, hpx]
    · have hpa : p a = false := by
        cases hp : p a
        · rfl
        · exact False.elim (hnd.1 ⟨x, hx', (hpf a hp).symm⟩)
      simp [List.find?, hpa, ih hnd.2 hx']

private theorem single_leak_clean_snoc {interp : ExternInterpretation} {r : ProtocolSetup}
    (hwf : ProtocolSetupWF r) {S : OpaqueSymbolSemantics} {who : List Participant} {ok : Nat → Bool}
    {t_clean : CliTurn} {accepted : List HwBytes}
    {g₀ : Ghost} {ms₀ : List Move} {τ_acc : List MachineEvent} {k : HwBytes}
    (hc₀ : Clean interp r S who ok g₀ ms₀ τ_acc)
    (hrel₀ : PureCRel interp r S who ok (t_clean.leakRecords r) t_clean.sent accepted τ_acc)
    (hopk₀ : COpkRelC interp r S who ok (t_clean.opkUsed r) τ_acc)
    (hk : KeyInDirsV1 r t_clean k) :
    ∃ m, Clean interp r S who ok g₀ (ms₀ ++ [m]) (τ_acc ++ [.leak k]) := by
  have hk' : LeakableSecret r (pureStripPrev (t_clean.leakRecords r)) (t_clean.opkUsed r) k :=
    (leakableSecret_pureStripPrev_iff r (t_clean.leakRecords r) (t_clean.opkUsed r) k).mp hk
  have hrecInv : TR.PureTRRecordStateInv interp r S zAnyPure g₀ ms₀
      (pureStripPrev (t_clean.leakRecords r)) :=
    trRecordStateInv_pureStripPrev (Z := zAnyPure) (fun _ _ => trivial) (hrel₀.recs hc₀)
  have hstep : ∃ m, LeakKind m ∧
      MatchedPrefix interp r S who g₀ (ms₀ ++ [m]) (τ_acc ++ [.leak k]) := by
    rcases TR.leakableSecret_cases hk' with hs | ⟨p, rec_env, hpb, hkey_env⟩
    · obtain ⟨m, hm, hmp', _⟩ := TR.setupLeak_step hwf.1 hc₀.1.1 hs (fun hw hu => hopk₀.apply hw hu hc₀)
      have hlk : LeakKind m := by cases m <;> cases hm <;> trivial
      exact ⟨m, hlk, hmp'⟩
    · obtain ⟨_, rec, st, stateIdx, heq_bytes, hget, hcurr, hsr, hkeys, _, _, hnd⟩ :=
        hrecInv p (recordBytes rec_env) hpb
      have hkey : KeyInRecord rec k := TR.keyInRecord_of_recordBytes_eq heq_bytes hkey_env
      have hrk_eq : rec.current.rootKey = gamma interp S g₀ st.rk := by
        simpa [TR.eraseSkipped, TR.eraseUnmodelled, TR.sessionOf] using congrArg SessionRec.rootKey hsr.2
      have hsc_eq : rec.current.senderChain =
          (TR.sessionOf interp (gamma interp S g₀) st).senderChain := by
        simpa [TR.eraseSkipped, TR.eraseUnmodelled] using congrArg SessionRec.senderChain hsr.2
      have hrc_eq : rec.current.receiverChains.map (fun c => { c with messageKeys := [] }) =
          (TR.sessionOf interp (gamma interp S g₀) st).receiverChains := by
        simpa [TR.eraseSkipped, TR.eraseUnmodelled] using congrArg SessionRec.receiverChains hsr.2
      have hpq_eq : rec.current.pqRatchetState = gamma interp S g₀ st.spqr := by
        simpa [TR.eraseSkipped, TR.eraseUnmodelled, TR.sessionOf] using
          congrArg SessionRec.pqRatchetState hsr.2
      have hnocs : ∀ ev ∈ ([MachineEvent.leak k] : List MachineEvent),
          eventKind ev ≠ .recv ∧ eventKind ev ≠ .pt := by
        intro ev hev; rw [List.mem_singleton.mp hev]; simp [eventKind]
      rcases hkey with rfl | ⟨sc, hsc, rfl | ⟨ck, hck, rfl⟩⟩ |
          ⟨rc, hrc, ⟨hne, _⟩ | ⟨ck, hck, rfl⟩ | ⟨mk, hmk, rfl⟩⟩ | rfl
      · exact ⟨.exposeKey p stateIdx .rk, trivial,
          TR.matchedPrefix_snoc_env hc₀.1.1
            (TR.modelRun_snoc_exposeKey r ms₀ p stateIdx .rk hc₀.1.1.2.1 hcurr)
            rfl rfl hnocs
            (by rw [TR.visOf_exposeKey_rk hget]; intro _ hv; rw [List.mem_singleton.mp hv]; rintro ⟨⟩)
            (by rw [TR.visOf_exposeKey_rk hget]; exact .cons ⟨rfl, _, rfl, .inl hrk_eq⟩ .nil)⟩
      · rw [hsc_eq] at hsc; dsimp only [TR.sessionOf] at hsc; injection hsc with hsc'; subst hsc'
        exact ⟨.exposeKey p stateIdx .dhs, trivial,
          TR.matchedPrefix_snoc_env hc₀.1.1
            (TR.modelRun_snoc_exposeKey r ms₀ p stateIdx .dhs hc₀.1.1.2.1 hcurr)
            rfl rfl hnocs
            (by rw [TR.visOf_exposeKey_dhs hget]; intro _ hv; rw [List.mem_singleton.mp hv]; rintro ⟨⟩)
            (by rw [TR.visOf_exposeKey_dhs hget]; exact .cons ⟨rfl, _, rfl, .inr rfl⟩ .nil)⟩
      · rw [hsc_eq] at hsc; dsimp only [TR.sessionOf] at hsc; injection hsc with hsc'; subst hsc'
        dsimp only at hck; injection hck with hck'; subst hck'
        exact ⟨.exposeKey p stateIdx .cks, trivial,
          TR.matchedPrefix_snoc_env hc₀.1.1
            (TR.modelRun_snoc_exposeKey r ms₀ p stateIdx .cks hc₀.1.1.2.1 hcurr)
            rfl rfl hnocs
            (by rw [TR.visOf_exposeKey_cks hget]; intro _ hv; rw [List.mem_singleton.mp hv]; rintro ⟨⟩)
            (by rw [TR.visOf_exposeKey_cks hget]; exact .cons ⟨rfl, _, rfl, .inl rfl⟩ .nil)⟩
      · have hmem_map : { rc with messageKeys := [] } ∈
            rec.current.receiverChains.map (fun c => { c with messageKeys := [] }) :=
          List.mem_map.mpr ⟨rc, hrc, rfl⟩
        rw [hrc_eq] at hmem_map; dsimp only [TR.sessionOf] at hmem_map
        obtain ⟨_, _, hc₀_eq⟩ := List.mem_map.mp hmem_map
        exact absurd (congrArg ChainRec.senderRatchetKeyPrivate hc₀_eq).symm hne
      · have hmem_map : { rc with messageKeys := [] } ∈
            rec.current.receiverChains.map (fun c => { c with messageKeys := [] }) :=
          List.mem_map.mpr ⟨rc, hrc, rfl⟩
        rw [hrc_eq] at hmem_map; dsimp only [TR.sessionOf] at hmem_map
        obtain ⟨c₀, hc₀_mem, hc₀_eq⟩ := List.mem_map.mp hmem_map
        have hck_eq : rc.chainKey =
            some (c₀.index.toBitVec, gamma interp S g₀ c₀.chainKey) :=
          (congrArg ChainRec.chainKey hc₀_eq).symm
        rw [hck_eq] at hck; injection hck with hck'; subst hck'
        have hmap_srk : st.recv.map (fun c => TR.serializedKey (gamma interp S g₀ c.ratchetKey)) =
            rec.current.receiverChains.map ChainRec.senderRatchetKey := by
          have h1 := congrArg (List.map ChainRec.senderRatchetKey) hrc_eq.symm
          rw [List.map_map] at h1; dsimp only [TR.sessionOf] at h1; rw [List.map_map] at h1
          exact h1
        have hnd_recv :
            (st.recv.map (fun c => TR.serializedKey (gamma interp S g₀ c.ratchetKey))).Nodup := by
          rw [hmap_srk]; exact hnd.1
        have hfind : _root_.DY.Libsignal.TripleRatchet.findRecvChain st.recv c₀.ratchetKey = some c₀ :=
          find?_eq_some_of_mem_nodup
            (fun c => TR.serializedKey (gamma interp S g₀ c.ratchetKey))
            hnd_recv hc₀_mem (·.ratchetKey == c₀.ratchetKey) (beq_self_eq_true _)
            (fun _ hy => by rw [beq_iff_eq.mp hy])
        exact ⟨.exposeKey p stateIdx (.ckr c₀.ratchetKey), trivial,
          TR.matchedPrefix_snoc_env hc₀.1.1
            (TR.modelRun_snoc_exposeKey r ms₀ p stateIdx (.ckr c₀.ratchetKey) hc₀.1.1.2.1 hcurr)
            rfl rfl hnocs
            (by rw [TR.visOf_exposeKey_ckr hget hfind]; intro _ hv; rw [List.mem_singleton.mp hv]; rintro ⟨⟩)
            (by rw [TR.visOf_exposeKey_ckr hget hfind]; exact .cons ⟨rfl, _, rfl, .inl rfl⟩ .nil)⟩
      · obtain ⟨pk, rIdx, srcIdx, skIdx, seed, hlog, _, hru, hgam, _⟩ := hkeys rc hrc mk hmk
        rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at hlog
        exact ⟨.exposeSkipped skIdx, trivial,
          TR.matchedPrefix_snoc_env hc₀.1.1
            (TR.modelRun_snoc_exposeSkipped r ms₀ skIdx hc₀.1.1.2.1)
            rfl rfl hnocs
            (by rw [TR.visOf_exposeSkipped hlog hru]; intro _ hv; rw [List.mem_singleton.mp hv]; rintro ⟨⟩)
            (by rw [TR.visOf_exposeSkipped hlog hru]; exact .cons ⟨rfl, _, rfl, .inl hgam.symm⟩ .nil)⟩
      · exact ⟨.exposeSpqr p stateIdx, trivial,
          TR.matchedPrefix_snoc_env hc₀.1.1
            (TR.modelRun_snoc_exposeSpqr r ms₀ p stateIdx hc₀.1.1.2.1 hcurr)
            rfl rfl hnocs
            (by rw [TR.visOf_exposeSpqr hget]; intro _ hv; rw [List.mem_singleton.mp hv]; rintro ⟨⟩)
            (by rw [TR.visOf_exposeSpqr hget]; exact .cons ⟨rfl, _, rfl, .inl hpq_eq⟩ .nil)⟩
  obtain ⟨m, hlk, hmp'⟩ := hstep
  exact ⟨m, clean_snoc_leakKind hc₀ hlk hmp'⟩

private theorem cliLiveAtCli_leak_single (hGood : GoodExit0CutSpec)
    {interp' : ExternInterpretation} {r : ProtocolSetup} (hwf : ProtocolSetupWF r) {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool}
    {t_clean : CliTurn} {accepted : List HwBytes} {σ_acc : List MachineEvent} {k : HwBytes}
    (hk : KeyInDirsV1 r t_clean k)
    (hlive : CliLiveAtCli interp' r S who ok t_clean accepted σ_acc) :
    CliLiveAtCli interp' r S who ok t_clean accepted (σ_acc ++ [.leak k]) := by
  have hleaks1 : ∀ e ∈ ([MachineEvent.leak k] : List MachineEvent),
      ∃ k', KeyInDirsV1 r t_clean k' ∧ e = .leak k' := by
    intro e he; rw [List.mem_singleton.mp he]; exact ⟨k, hk, rfl⟩
  have hnonRng1 : ∀ e ∈ ([MachineEvent.leak k] : List MachineEvent), eventKind e ≠ .rng := by
    intro e he; rw [List.mem_singleton.mp he]; simp [eventKind]
  have hhead_nonRng1 : ∀ y, ([MachineEvent.leak k] : List MachineEvent).head? = some y →
      eventKind y ≠ .rng := by
    intro y hy; simp only [List.head?_cons, Option.some.injEq] at hy; subst hy; simp [eventKind]
  have hhead_leak1 : ∀ e ∈ ([MachineEvent.leak k] : List MachineEvent).head?,
      eventKind e = .leak := by
    intro e he
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at he
    subst he; rfl
  refine
    { noAdjRng := noAdjRng_append_of_head_nonRng hlive.noAdjRng trivial hhead_nonRng1
      witness := ?_
      cutRel := fun τ' hinh' => ?_ }
  · obtain ⟨τ_acc, g₀, ms₀, hex₀, hnrc₀⟩ := hlive.witness
    obtain ⟨_, hrel₀, hopk₀⟩ := hlive.cliLiveAt_of_cut ⟨g₀, ms₀, hex₀, hnrc₀⟩
    have hc₀ : Clean interp' r S who ok g₀ ms₀ τ_acc := explainsCli_toClean hex₀ hnrc₀
    obtain ⟨m, hc₁⟩ := single_leak_clean_snoc hwf hc₀ hrel₀ hopk₀ hk
    have hcs_blk : CoinSplit [.leak k] [.leak k] :=
      coinSplit_leaks (fun e he => ⟨k, List.mem_singleton.mp he⟩)
    have hgood_blk : GoodStepCut ok (callStarts τ_acc).length [.leak k] :=
      GoodStepCut.leaks (fun e he => ⟨k, List.mem_singleton.mp he⟩)
    obtain ⟨hex₁, hnrc₁⟩ :=
      hGood hex₀ hcs_blk hgood_blk (Or.inl rfl) (fun _ _ _ => rfl) hc₁
    exact ⟨τ_acc ++ [.leak k], g₀, ms₀ ++ [m], hex₁, hnrc₁⟩
  · obtain ⟨g', ms', hex', hnrc'⟩ := hinh'
    obtain ⟨τ'_pre, rfl, hcs_pre⟩ := coinSplit_append_of_all_nonRng hnonRng1 hex'.1
    have hclean' : Clean interp' r S who ok g' ms' (τ'_pre ++ [.leak k]) :=
      explainsCli_toClean hex' hnrc'
    obtain ⟨ms_pre, δ, rfl, hmp_pre, _⟩ :=
      matchedPrefix_split_all_leak hwf.1 hclean'.matched hhead_leak1
    have hclean_pre : Clean interp' r S who ok g' ms_pre τ'_pre :=
      clean_prefix (matchedPrefix_length_eq hmp_pre) hclean'
    have hex_pre : ExplainsCli interp' r S who ok σ_acc τ'_pre g' ms_pre :=
      explainsCli_prefix hcs_pre hmp_pre hclean_pre.1.2 hex'
    obtain ⟨hclean_inh_pre, hrel_pre, hopk_pre⟩ :=
      hlive.cliLiveAt_of_cut ⟨g', ms_pre, hex_pre, hclean_pre.2⟩
    exact (cliLeak_step hwf hleaks1 hclean_inh_pre hrel_pre hopk_pre).2

/-- Base initialization, `clearSession`, and `.leak` stepping for `CliLiveAtCli`. -/
theorem init_clear_leak (hGood : GoodExit0CutSpec) : InitClearLeakSpec := by
  refine ⟨?_, ?_, ?_⟩
  · intro interp' r S hwf hS who ok
    have hc_nil := init_clean_nil hwf hS who ok
    refine
      { noAdjRng := trivial
        witness := ⟨[], ⟨r.fresh, fun _ => []⟩, [], explainsCli_nil hc_nil, hc_nil.2⟩
        cutRel := fun τ' hinh => ?_ }
    obtain ⟨_, _, hex', _⟩ := hinh
    cases hex'.1
    refine ⟨?_, cOpkRelC_nil⟩
    rw [cliInit_leakRecords_eq_none]
    exact pureCRel_nil hwf S who ok
  · intro interp' r S who ok t_clean accepted σ_acc p hlive
    refine
      { noAdjRng := hlive.noAdjRng
        witness := hlive.witness
        cutRel := fun τ' hinh => ?_ }
    obtain ⟨hrel, hopk⟩ := hlive.cutRel τ' hinh
    exact ⟨pureCRel_clearSession p hrel, cOpkRelC_clearSession p hopk⟩
  · intro interp' r S who ok t_clean accepted σ_acc leaks hwf hleaks hlive
    induction leaks generalizing σ_acc with
    | nil =>
      rw [List.append_nil]
      exact hlive
    | cons e tl ih =>
      obtain ⟨k, hk, rfl⟩ := hleaks e (List.mem_cons_self ..)
      have hlive' := cliLiveAtCli_leak_single hGood hwf hk hlive
      have hres := ih (fun e' he' => hleaks e' (List.mem_cons_of_mem _ he')) hlive'
      rwa [List.append_assoc] at hres

end Symbolic.Swarm.Coinsplit.Lift.L01
