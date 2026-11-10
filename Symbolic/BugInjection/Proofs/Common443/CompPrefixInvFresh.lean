/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.CompFreshDistinct
public import Symbolic.BugInjection.Proofs.Common443.CompExcuse
public import Symbolic.BugInjection.Proofs.Common443.CompPrefixInvBundle
public import Symbolic.BugInjection.Proofs.Common443.CompPrefixInvEnc
public import Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice
public import Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse

@[expose] public section
set_option autoImplicit false
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Common443.CompPrefixInvFresh
open ByteSpecs DY DY.Libsignal.Composed DY.Libsignal.Composed.Refinement
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (MachineEvent)
open Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Proofs.Common443.CompExcuse Symbolic.BugInjection.Proofs.Common443.CompFreshDistinct Symbolic.BugInjection.Proofs.Common443.CompPrefixInvStruct Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice Symbolic.BugInjection.Proofs.Common443.CompPrefixInvBundle Symbolic.BugInjection.Proofs.Common443.CompPrefixInvEnc Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompTrace
open Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse (concatPrefixes_nil concatPrefixes_cons concatPrefixes_append_eq bool_serialize_singleton slowNat_serialize_zero slowNat_serialize_succ slowBytes_serialize_eq slowString_serialize_eq uint32_serialize_singleton x25519Key_dhPk_eq length_nil_eq length_append_entry_eq getMessageSentAt_eq_at?)
cref_open
theorem gamma_randTerm_eq_of_ne_zero (i : ExternInterpretation) (S : Sem) (g : Ghost) (ts sz : Nat) (hsz : sz ≠ 0) : gamma i S g (randTerm ts sz) = g.σ ts sz := by unfold gamma; rw [CompExcuse.gamma'_randTerm i S g ts sz hsz]
theorem freshSafeTerm_randTerm_zero (i : ExternInterpretation) (S : Sem) (g : Ghost) (ts : Nat) : FreshSafeTerm i S g (randTerm ts 0) := by intro x hx _ _ _; unfold gamma' randTerm at hx; change x ∈ ((({ timestamp := ts, size := 0 } : DY.Random.Random DY.Bytes).pack).rec (gAll i S g)).memo at hx; rw [DY.Bytes.rec_eq (gRandom g) (gAll i S g)] at hx; simp [gRandom, concretizeRandom] at hx
theorem freshSafeTerm_randTerm_of_single_rng {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {b : HwBytes} {ts sz : Nat} {anc : Option Nat} (hem : EventMatchesEntry i r S g (.rng b) { kind := .rng, terms := [randTerm ts sz], layout := .single, anchor := anc }) (hb : ∀ t ∈ ([11, 16, 17] : List Nat), b ≠ fillFresh t 64) : FreshSafeTerm i S g (randTerm ts sz) ∧ (sz ≠ 0 → g.σ ts sz = b ∧ ∀ t ∈ ([11, 16, 17] : List Nat), g.σ ts sz ≠ fillFresh t 64) := by
  by_cases hsz : sz = 0
  · subst hsz; exact ⟨freshSafeTerm_randTerm_zero i S g ts, fun h => False.elim (h rfl)⟩
  · obtain ⟨_, hmap⟩ := hem; dsimp only [List.map, eventBytes] at hmap; injection hmap with hγ
    rw [gamma_randTerm_eq_of_ne_zero i S g ts sz hsz] at hγ
    have hne : ∀ t ∈ ([11, 16, 17] : List Nat), g.σ ts sz ≠ fillFresh t 64 := fun t ht => hγ ▸ hb t ht
    exact ⟨freshSafeTerm_randTerm_of_ne_fillFresh64 i S g ts sz hne, fun _ => ⟨hγ, hne⟩⟩
theorem freshSafeTerm_randTerm_of_single_pt_len {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {b : HwBytes} {ts sz : Nat} {anc : Option Nat} (hem : EventMatchesEntry i r S g (.pt b) { kind := .pt, terms := [randTerm ts sz], layout := .single, anchor := anc }) (hlen : b.length ≠ 64) : FreshSafeTerm i S g (randTerm ts sz) ∧ (sz ≠ 0 → g.σ ts sz = b ∧ (g.σ ts sz).length ≠ 64) := by
  by_cases hsz : sz = 0
  · subst hsz; exact ⟨freshSafeTerm_randTerm_zero i S g ts, fun h => False.elim (h rfl)⟩
  · obtain ⟨_, hmap⟩ := hem; dsimp only [List.map, eventBytes] at hmap; injection hmap with hγ
    rw [gamma_randTerm_eq_of_ne_zero i S g ts sz hsz] at hγ; have hlen' : (g.σ ts sz).length ≠ 64 := hγ ▸ hlen; exact ⟨freshSafeTerm_randTerm_of_ne_64 i S g ts sz hlen', fun _ => ⟨hγ, hlen'⟩⟩
theorem mem_setupRandomsAt_32 {r : Records} (hNe : r.alice ≠ r.bob) {ts : Nat} (h : (ts = 0 ∨ ts = 5 ∨ ts = 10) ∨ (r.withOpk = true ∧ ts = 22)) : (ts, 32) ∈ setupRandomsAt r := by
  rw [Symbolic.Swarm.CREF.b1_setupRandomsAt_eq r hNe]; rcases h with (rfl | rfl | rfl) | ⟨hopk, rfl⟩ <;> simp [*]
theorem mem_setupRandomsAt_64 (r : Records) (hNe : r.alice ≠ r.bob) {ts : Nat} (h : ts ∈ ([11, 16, 17] : List Nat)) : (ts, 64) ∈ setupRandomsAt r := by
  rw [Symbolic.Swarm.CREF.b1_setupRandomsAt_eq r hNe]; simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl <;> simp
theorem freshSafeTerm_setup_32 {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} (hcompat : Compat i r S g) (hwf : RecordsWF r) {ts : Nat} (hp : (ts, 32) ∈ setupRandomsAt r) : (g.σ ts 32).length = 32 ∧ FreshSafeTerm i S g (randTerm ts 32) := by
  have hlen : (g.σ ts 32).length = 32 := by rw [hcompat.1 (ts, 32) hp]; exact hwf.2.1 (ts, 32) hp
  exact ⟨hlen, freshSafeTerm_randTerm_of_ne_64 i S g ts 32 (by rw [hlen]; decide)⟩
theorem freshSafeTerm_setup_64 {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} (hcompat : Compat i r S g) (hNe : r.alice ≠ r.bob) (hsec3 : secretBytes r 3 = fillFresh 11 64) (hsec4 : secretBytes r 4 = fillFresh 16 64) (hsec5 : secretBytes r 5 = fillFresh 17 64) {ts : Nat} (hts : ts ∈ ([11, 16, 17] : List Nat)) : g.σ ts 64 = fillFresh ts 64 ∧ FreshSafeTerm i S g (randTerm ts 64) := by
  have hσ := hcompat.1 (ts, 64) (mem_setupRandomsAt_64 r hNe hts); simp only [List.mem_cons, List.not_mem_nil, or_false] at hts
  rcases hts with rfl | rfl | rfl
  · have h3 : r.fresh 11 64 = secretBytes r 3 := by unfold secretBytes; rw [Symbolic.Swarm.CREF.b1_setupRandomsAt_eq r hNe]; cases r.withOpk <;> rfl
    rw [h3, hsec3] at hσ; exact ⟨hσ, freshSafeTerm_randTerm_64_setup i S g (by decide) hσ⟩
  · have h4 : r.fresh 16 64 = secretBytes r 4 := by unfold secretBytes; rw [Symbolic.Swarm.CREF.b1_setupRandomsAt_eq r hNe]; cases r.withOpk <;> rfl
    rw [h4, hsec4] at hσ; exact ⟨hσ, freshSafeTerm_randTerm_64_setup i S g (by decide) hσ⟩
  · have h5 : r.fresh 17 64 = secretBytes r 5 := by unfold secretBytes; rw [Symbolic.Swarm.CREF.b1_setupRandomsAt_eq r hNe]; cases r.withOpk <;> rfl
    rw [h5, hsec5] at hσ; exact ⟨hσ, freshSafeTerm_randTerm_64_setup i S g (by decide) hσ⟩
theorem freshSafeTerm_setupSecret {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} (hcompat : Compat i r S g) (hwf : RecordsWF r) (hsec3 : secretBytes r 3 = fillFresh 11 64) (hsec4 : secretBytes r 4 = fillFresh 16 64) (hsec5 : secretBytes r 5 = fillFresh 17 64) (k : Nat) : FreshSafeTerm i S g (setupSecret r k) := by
  unfold setupSecret; rw [Symbolic.Swarm.CREF.TR.setupRandoms_eq r hwf.1]
  rcases k with _ | ⟨_ | ⟨_ | ⟨_ | ⟨_ | ⟨_ | ⟨_ | k⟩⟩⟩⟩⟩⟩
  · cases r.withOpk <;> exact (freshSafeTerm_setup_32 hcompat hwf (mem_setupRandomsAt_32 hwf.1 (.inl (.inl rfl)))).2
  · cases r.withOpk <;> exact (freshSafeTerm_setup_32 hcompat hwf (mem_setupRandomsAt_32 hwf.1 (.inl (.inr (.inl rfl))))).2
  · cases r.withOpk <;> exact (freshSafeTerm_setup_32 hcompat hwf (mem_setupRandomsAt_32 hwf.1 (.inl (.inr (.inr rfl))))).2
  · cases r.withOpk <;> exact (freshSafeTerm_setup_64 hcompat hwf.1 hsec3 hsec4 hsec5 (by decide)).2
  · cases r.withOpk <;> exact (freshSafeTerm_setup_64 hcompat hwf.1 hsec3 hsec4 hsec5 (by decide)).2
  · cases r.withOpk <;> exact (freshSafeTerm_setup_64 hcompat hwf.1 hsec3 hsec4 hsec5 (by decide)).2
  · cases hopk : r.withOpk
    · exact freshSafeTerm_randTerm_zero i S g 0
    · exact (freshSafeTerm_setup_32 hcompat hwf (mem_setupRandomsAt_32 hwf.1 (.inr ⟨hopk, rfl⟩))).2
  · cases r.withOpk <;> exact freshSafeTerm_randTerm_zero i S g 0
theorem setupSent_nil :
    List.filterMap (fun i => (Trace.nil : ExecTrace).getMessageSentAt i)
      (newIndices Trace.nil Trace.nil) = [] := by
  simp [newIndices, length_nil_eq]
private theorem newIndices_nil_append {E : Type} [ExecTraceTypes.Has E]
    (tr : ExecTrace) (e : E) :
    newIndices Trace.nil (tr.append e) = newIndices Trace.nil tr ++ [tr.length] := by
  simp only [newIndices, length_nil_eq, length_append_entry_eq,
    Nat.sub_zero, List.range'_concat, Nat.one_mul, Nat.zero_add]
private theorem filterMap_sent_prefix {E : Type} [ExecTraceTypes.Has E]
    (tr : ExecTrace) (e : E) :
    List.filterMap (fun i => (tr.append e).getMessageSentAt i) (newIndices Trace.nil tr) =
      List.filterMap (fun i => tr.getMessageSentAt i) (newIndices Trace.nil tr) := by
  apply List.filterMap_congr
  intro i hi
  simp only [newIndices, length_nil_eq, Nat.sub_zero, List.mem_range'_1, Nat.zero_add] at hi
  simp only [getMessageSentAt_eq_at?, Symbolic.Swarm.CREF.TR.at?_append_of_lt tr e hi.2]
theorem setupSent_append_net (tr : ExecTrace) (b : DY.Bytes) :
    List.filterMap (fun i => (tr.append (Symbolic.Swarm.CREF.TR.NetE b)).getMessageSentAt i)
      (newIndices Trace.nil (tr.append (Symbolic.Swarm.CREF.TR.NetE b))) =
      List.filterMap (fun i => tr.getMessageSentAt i) (newIndices Trace.nil tr) ++ [b] := by
  rw [newIndices_nil_append, List.filterMap_append, filterMap_sent_prefix]
  simp only [List.filterMap_cons, List.filterMap_nil, getMessageSentAt_eq_at?, Symbolic.Swarm.CREF.at?_append_length]; rfl
theorem setupSent_append_nonNet {E : Type} [ExecTraceTypes.Has E]
    (tr : ExecTrace) (e : E)
    (hproj : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) :
      Option DY.Network.ExecEntryT) = none) :
    List.filterMap (fun i => (tr.append e).getMessageSentAt i)
      (newIndices Trace.nil (tr.append e)) =
      List.filterMap (fun i => tr.getMessageSentAt i) (newIndices Trace.nil tr) := by
  rw [newIndices_nil_append, List.filterMap_append, filterMap_sent_prefix]
  simp only [List.filterMap_cons, List.filterMap_nil, getMessageSentAt_eq_at?, Symbolic.Swarm.CREF.at?_append_length, hproj, List.append_nil]
theorem freshSafeTerm_setupPublic {r : Records} {S : Sem} {g : Ghost} (hcompat : Compat compI0 r S g) (hwf : RecordsWF r) (hsec3 : secretBytes r 3 = fillFresh 11 64) (hsec4 : secretBytes r 4 = fillFresh 16 64) (hsec5 : secretBytes r 5 = fillFresh 17 64) (k : Nat) : FreshSafeTerm compI0 S g (setupPublic r k) := by
  have hsec := freshSafeTerm_setupSecret hcompat hwf hsec3 hsec4 hsec5
  have h0 : FreshSafeTerm compI0 S g (randTerm 0 32) := by rw [← setupSecret_0 hwf.1]; exact hsec 0
  have h1 : FreshSafeTerm compI0 S g (randTerm 5 32) := by rw [← setupSecret_1 hwf.1]; exact hsec 1
  have h2 : FreshSafeTerm compI0 S g (randTerm 10 32) := by rw [← setupSecret_2 hwf.1]; exact hsec 2
  have h3 : FreshSafeTerm compI0 S g (randTerm 11 64) := by rw [← setupSecret_3 hwf.1]; exact hsec 3
  have h4 : FreshSafeTerm compI0 S g (randTerm 16 64) := by rw [← setupSecret_4 hwf.1]; exact hsec 4
  have h5 : FreshSafeTerm compI0 S g (randTerm 17 64) := by rw [← setupSecret_5 hwf.1]; exact hsec 5
  rcases k with _ | ⟨_ | ⟨_ | ⟨_ | ⟨_ | ⟨_ | ⟨_ | ⟨_ | ⟨_ | k⟩⟩⟩⟩⟩⟩⟩⟩
  · rw [setupPublic_0 hwf.1]; exact freshSafeTerm_dhPk h0
  · rw [setupPublic_1 hwf.1]; exact freshSafeTerm_vk h0
  · rw [setupPublic_2 hwf.1]; exact freshSafeTerm_dhPk h1
  · rw [setupPublic_3 hwf.1]; exact freshSafeTerm_vk h1
  · rw [setupPublic_4 hwf.1]; exact freshSafeTerm_dhPk h2
  · rw [setupPublic_5 hwf.1]; exact freshSafeTerm_sign h1 h3 (freshSafeTerm_encodeEC compI0 S g (freshSafeTerm_dhPk h2))
  · rw [setupPublic_6 hwf.1]; exact freshSafeTerm_kemPk h4
  · rw [setupPublic_7 hwf.1]; exact freshSafeTerm_sign h1 h5 (freshSafeTerm_encodeKEM compI0 S g (freshSafeTerm_kemPk h4))
  · rw [setupPublic, setupSent, Symbolic.Swarm.CREF.TR.setupTrace_eq r hwf.1]; cases hopk : r.withOpk
    · simp only [Bool.false_eq_true, ↓reduceIte, Symbolic.Swarm.CREF.TR.setupTr4, Symbolic.Swarm.CREF.TR.setupTr3, Symbolic.Swarm.CREF.TR.setupTr2, Symbolic.Swarm.CREF.TR.setupTr1]
      repeat first | rw [setupSent_append_net] | rw [setupSent_append_nonNet _ _ rfl]
      rw [setupSent_nil]; exact freshSafeTerm_randTerm_zero compI0 S g 0
    · simp only [↓reduceIte, Symbolic.Swarm.CREF.TR.setupTr5, Symbolic.Swarm.CREF.TR.setupTr4, Symbolic.Swarm.CREF.TR.setupTr3, Symbolic.Swarm.CREF.TR.setupTr2, Symbolic.Swarm.CREF.TR.setupTr1]
      repeat first | rw [setupSent_append_net] | rw [setupSent_append_nonNet _ _ rfl]
      rw [setupSent_nil]; exact freshSafeTerm_dhPk (freshSafeTerm_setup_32 hcompat hwf (mem_setupRandomsAt_32 hwf.1 (.inr ⟨hopk, rfl⟩))).2
  · rw [setupPublic, setupSent, Symbolic.Swarm.CREF.TR.setupTrace_eq r hwf.1]
    cases r.withOpk <;> (
      simp only [Bool.false_eq_true, ↓reduceIte, Symbolic.Swarm.CREF.TR.setupTr5, Symbolic.Swarm.CREF.TR.setupTr4, Symbolic.Swarm.CREF.TR.setupTr3, Symbolic.Swarm.CREF.TR.setupTr2, Symbolic.Swarm.CREF.TR.setupTr1]
      repeat first | rw [setupSent_append_net] | rw [setupSent_append_nonNet _ _ rfl]
      rw [setupSent_nil]; exact freshSafeTerm_randTerm_zero compI0 S g 0)
theorem forall2_exists_left {α β : Type} {R : α → β → Prop} {as : List α} {bs : List β} (h : List.Forall₂ R as bs) {b : β} (hb : b ∈ bs) : ∃ a ∈ as, R a b := by
  induction h with
  | nil => cases hb
  | cons hhead _ ih =>
    rcases List.mem_cons.mp hb with rfl | hmem
    · exact ⟨_, List.mem_cons_self .., hhead⟩
    · obtain ⟨a, ha, hr⟩ := ih hmem; exact ⟨a, List.mem_cons_of_mem _ ha, hr⟩
theorem event_eq_rng_of_matches_rng {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {ev : MachineEvent} {ts : List DY.Bytes} {lay : VisByteLayout} {anc : Option Nat} (hem : EventMatchesEntry i r S g ev { kind := .rng, terms := ts, layout := lay, anchor := anc }) : ∃ b : HwBytes, ev = .rng b := by have hk := hem.1; cases ev <;> simp [eventKind] at hk; exact ⟨_, rfl⟩
theorem freshSafeTerm_draws_of_aliceVis {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {tr₁ : ExecTrace} {a b : Participant} {o : DY.Libsignal.PQXDH.AliceHandshakeOut} {hb : DY.Libsignal.PQXDH.BundleHandles} {bun : HwBytes} {rs : List MachineEvent} (hm₀ : List.Forall₂ (EventMatchesEntry i r S g) (.recv bun :: rs) (aliceVis tr₁ (iniAliceStartTr tr₁ a b o) hb)) (hrs : ∀ b : HwBytes, .rng b ∈ rs → ∀ t ∈ ([11, 16, 17] : List Nat), b ≠ fillFresh t 64) : FreshSafeTerm i S g (randTerm tr₁.length 32) ∧ (∀ t ∈ ([11, 16, 17] : List Nat), g.σ tr₁.length 32 ≠ fillFresh t 64) ∧ FreshSafeTerm i S g (randTerm (tr₁.length + 1) 32) ∧ (g.σ (tr₁.length + 1) 32).length = 32 ∧ FreshSafeTerm i S g (randTerm (tr₁.length + 2) 32) ∧ (∀ t ∈ ([11, 16, 17] : List Nat), g.σ (tr₁.length + 2) 32 ≠ fillFresh t 64) := by
  rw [aliceVis_iniAliceStartTr] at hm₀; obtain ⟨ev_ek, hev_ek_mem, hem_ek⟩ := forall2_exists_left hm₀ (by simp : rngEntry (randTerm tr₁.length 32) ∈ _); obtain ⟨b_ek, rfl⟩ := event_eq_rng_of_matches_rng hem_ek
  have hek := freshSafeTerm_randTerm_of_single_rng hem_ek
    (hrs b_ek ((List.mem_cons.mp hev_ek_mem).resolve_left (by nofun)))
  have hmem_ent : ({ kind := .rng, terms := [randTerm (tr₁.length + 1) 32], layout := .kyberCoin 0, anchor := none } : VisEntry) ∈
      ({ kind := .recv, terms := received tr₁ ([hb.spk, hb.spkSig, hb.pqpk, hb.pqpkSig] ++ hb.opk.toList), layout := .bundle, anchor := none } :: rngEntry (randTerm tr₁.length 32) :: (kyberCoinEntries (randTerm (tr₁.length + 1) 32) ++
         [{ rngEntry (randTerm (tr₁.length + 2) 32) with anchor := some (tr₁.length + 5) }])) := by
    refine List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _ ?_)); unfold kyberCoinEntries; exact List.mem_map.mpr ⟨0, by decide, rfl⟩
  obtain ⟨_, _, _, _, t, ht, hlen, _⟩ := forall2_exists_left hm₀ hmem_ent
  injection ht with ht_eq; subst ht_eq
  rw [gamma_randTerm_eq_of_ne_zero i S g (tr₁.length + 1) 32 (by decide)] at hlen
  obtain ⟨ev_dhs, hev_dhs_mem, hem_dhs⟩ := forall2_exists_left hm₀
    (by simp : ({ rngEntry (randTerm (tr₁.length + 2) 32) with anchor := some (tr₁.length + 5) } : VisEntry) ∈ _)
  obtain ⟨b_dhs, rfl⟩ := event_eq_rng_of_matches_rng hem_dhs
  have hdhs := freshSafeTerm_randTerm_of_single_rng hem_dhs
    (hrs b_dhs ((List.mem_cons.mp hev_dhs_mem).resolve_left (by nofun)))
  exact ⟨hek.1, (hek.2 (by decide)).2,
    freshSafeTerm_randTerm_of_ne_64 i S g (tr₁.length + 1) 32 (by rw [hlen]; decide), hlen,
    hdhs.1, (hdhs.2 (by decide)).2⟩
private theorem at?_append_eq_of_eq {T S : Type} [ExecTraceTypes.Has T] [ExecTraceTypes.Has S] (tr : ExecTrace) (x : S) {i : Nat} (hi : i = tr.length) : ((tr.append x).at? i : Option T) = TraceEntryHas.proj (TraceEntryHas.inj x : ExecTrace.Entry) := by
  subst hi; exact Symbolic.Swarm.CREF.at?_append_length tr x
@[simp] private theorem length_append_entry {T : Type} [ExecTraceTypes.Has T]
    (tr : ExecTrace) (x : T) : (tr.append x).length = tr.length + 1 := length_append_entry_eq tr x
local macro "at?_encNextTr_tac" : tactic =>
  `(tactic| (dsimp only [encNextTr, encPreSaltTr]
             repeat (rw [Symbolic.Swarm.CREF.TR.at?_append_of_lt _ _ (by simp only [length_append_entry]; omega)])
             rw [at?_append_eq_of_eq _ _ (by simp [length_append_entry])]; rfl))
theorem newRandoms_encNextTr (tr₂ : ExecTrace) (me : Participant) (sIdx : Nat) (stA : DY.Libsignal.TripleRatchet.TRState) (cl pq : Nat) : newRandoms tr₂ (encNextTr tr₂ me sIdx stA cl pq) = [(randTerm tr₂.length 32, 32), (randTerm (tr₂.length + 1) cl, cl)] := by
  unfold newRandoms newIndices; have hlen : (encNextTr tr₂ me sIdx stA cl pq).length = tr₂.length + 7 := (by unfold encNextTr encPreSaltTr; simp only [length_append_entry]); rw [hlen, Nat.add_sub_cancel_left]; simp only [List.range', Nat.add_assoc]
  have h0 : ((encNextTr tr₂ me sIdx stA cl pq).at? tr₂.length : Option DY.Random.ExecEntryT) = some (RndE 32) := by at?_encNextTr_tac
  have h1 : ((encNextTr tr₂ me sIdx stA cl pq).at? (tr₂.length + 1) : Option DY.Random.ExecEntryT) = some (RndE cl) := by at?_encNextTr_tac
  have h2 : ((encNextTr tr₂ me sIdx stA cl pq).at? (tr₂.length + 2) : Option DY.Random.ExecEntryT) = none := by at?_encNextTr_tac
  have h3 : ((encNextTr tr₂ me sIdx stA cl pq).at? (tr₂.length + 3) : Option DY.Random.ExecEntryT) = none := by at?_encNextTr_tac
  have h4 : ((encNextTr tr₂ me sIdx stA cl pq).at? (tr₂.length + 4) : Option DY.Random.ExecEntryT) = none := by at?_encNextTr_tac
  have h5 : ((encNextTr tr₂ me sIdx stA cl pq).at? (tr₂.length + 5) : Option DY.Random.ExecEntryT) = none := by at?_encNextTr_tac
  have h6 : ((encNextTr tr₂ me sIdx stA cl pq).at? (tr₂.length + 6) : Option DY.Random.ExecEntryT) = none := by at?_encNextTr_tac
  simp [h0, h1, h2, h3, h4, h5, h6, RndE]
theorem encVis_encNextTr_of_forall2_three {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {tr₂ : ExecTrace} {me : Participant} {sIdx : Nat} {stA : DY.Libsignal.TripleRatchet.TRState} {cl pq : Nat} {wr : Nat × Nat} {pt c w : HwBytes} (hm₁ : List.Forall₂ (EventMatchesEntry i r S g) [.pt pt, .rng c, .send w] (encVis tr₂ (encNextTr tr₂ me sIdx stA cl pq) (some wr) true)) : cl ≠ 0 ∧ EventMatchesEntry i r S g (.pt pt) ⟨.pt, [randTerm tr₂.length 32], .single, none⟩ ∧ EventMatchesEntry i r S g (.rng c) (rngEntry (randTerm (tr₂.length + 1) cl)) ∧ EventMatchesEntry i r S g (.send w) ⟨.send, received tr₂ [wr.1, wr.2] ++ [encOut tr₂ stA cl pq], .preKeySend, none⟩ := by
  unfold encVis encSend at hm₁; rw [newRandoms_encNextTr, lastSent_encNextTr] at hm₁
  by_cases hcl : cl = 0
  · subst hcl; simp [encDraws] at hm₁
  · have hne : (cl != 0) = true := bne_iff_ne.mpr hcl; simp only [encDraws, List.filter_cons, hne, ↓reduceIte, List.filter_nil, List.map_cons, List.map_nil, List.cons_append, List.nil_append] at hm₁
    rcases hm₁ with (_ | ⟨hpt, _ | ⟨hrng, _ | ⟨hsend, _⟩⟩⟩)
    exact ⟨hcl, hpt, hrng, hsend⟩
theorem freshSafeTerm_draws_of_encVis {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {tr₂ : ExecTrace} {me : Participant} {sIdx : Nat} {stA : DY.Libsignal.TripleRatchet.TRState} {cl pq : Nat} {wr : Nat × Nat} {pt c w : HwBytes} (hm₁ : List.Forall₂ (EventMatchesEntry i r S g) [.pt pt, .rng c, .send w] (encVis tr₂ (encNextTr tr₂ me sIdx stA cl pq) (some wr) true)) (hpt : pt.length ≠ 64) (hc : ∀ t ∈ ([11, 16, 17] : List Nat), c ≠ fillFresh t 64) : cl ≠ 0 ∧ FreshSafeTerm i S g (randTerm tr₂.length 32) ∧ (g.σ tr₂.length 32).length ≠ 64 ∧ FreshSafeTerm i S g (randTerm (tr₂.length + 1) cl) ∧ (∀ t ∈ ([11, 16, 17] : List Nat), g.σ (tr₂.length + 1) cl ≠ fillFresh t 64) := by obtain ⟨hcl, hem_pt, hem_rng, _⟩ := encVis_encNextTr_of_forall2_three hm₁; have hpt_safe := freshSafeTerm_randTerm_of_single_pt_len hem_pt hpt; have hc_safe := freshSafeTerm_randTerm_of_single_rng hem_rng hc; exact ⟨hcl, hpt_safe.1, (hpt_safe.2 (by decide)).2, hc_safe.1, (hc_safe.2 hcl).2⟩
theorem x25519Key_dhPk (sk : DY.Bytes) : DY.X25519.x25519Key (DY.DiffieHellman.dhPk sk) = DY.DiffieHellman.dhPk sk := x25519Key_dhPk_eq sk
theorem x25519Key_setupPublic_2 {r : Records} (hNe : r.alice ≠ r.bob) : DY.X25519.x25519Key (setupPublic r 2) = setupPublic r 2 := by rw [setupPublic_2 hNe]; exact x25519Key_dhPk _
theorem x25519Key_setupPublic_4 {r : Records} (hNe : r.alice ≠ r.bob) : DY.X25519.x25519Key (setupPublic r 4) = setupPublic r 4 := by rw [setupPublic_4 hNe]; exact x25519Key_dhPk _
theorem freshSafeTerm_spqrSendKey {i : ExternInterpretation} {S : Sem} {g : Ghost} {st coins : DY.Bytes} (hst : FreshSafeTerm i S g st) (hc : FreshSafeTerm i S g coins) : FreshSafeTerm i S g (DY.Spqr.spqrSend st coins).2.1 := by
  have hv := DY.Bytes.pack_view? DY.Spqr.InitState.SubF st; unfold DY.Spqr.spqrSend; dsimp only; split
  · rename_i a p heq; rw [heq] at hv; simp only at hv; subst hv
    have ha : FreshSafeTerm i S g a := fun x hx t ht hval => hst x
      (by unfold gamma' at hx ⊢; rw [DY.Bytes.rec_eq (gSpqrInit S) (gAll i S g)]; exact List.mem_append_left _ (by simpa using hx)) t ht hval
    have hp : FreshSafeTerm i S g p := fun x hx t ht hval => hst x
      (by unfold gamma' at hx ⊢; rw [DY.Bytes.rec_eq (gSpqrInit S) (gAll i S g)]; exact List.mem_append_right _ (by simpa using hx)) t ht hval
    exact freshSafeTerm_spqrChainKey ha hp (freshSafeTerm_lit_of_length_ne_64 i S g _ (by decide))
  · refine freshSafeTerm_of_opaqueNode (ts := [st, coins]) ?_
      (fun _ hu => (List.mem_cons.mp hu).elim (· ▸ hst) (fun h => List.mem_singleton.mp h ▸ hc))
    unfold gamma'; rw [DY.Bytes.rec_eq (gSpqrSendKey S) (gAll i S g)]; rfl
theorem freshSafeTerm_aliceOut {S : Sem} {g : Ghost} {tr₁ : ExecTrace} {ikA ikB spk pqpk : DY.Bytes} (hikA : FreshSafeTerm compI0 S g ikA) (hikB : FreshSafeTerm compI0 S g ikB) (hikB_key : FreshSafeTerm compI0 S g (DY.X25519.x25519Key ikB)) (hspk : FreshSafeTerm compI0 S g spk) (hspk_key : FreshSafeTerm compI0 S g (DY.X25519.x25519Key spk)) (hpqpk : FreshSafeTerm compI0 S g pqpk) (hek : FreshSafeTerm compI0 S g (randTerm tr₁.length 32)) (hent : FreshSafeTerm compI0 S g (randTerm (tr₁.length + 1) 32)) : let o := iniAliceOut tr₁ ikA ikB spk pqpk none; FreshSafeTerm compI0 S g o.ikA ∧ FreshSafeTerm compI0 S g o.ikB ∧ FreshSafeTerm compI0 S g o.spk ∧ FreshSafeTerm compI0 S g o.pqpk ∧ FreshSafeTerm compI0 S g o.ek ∧ FreshSafeTerm compI0 S g o.ct ∧ FreshSafeTerm compI0 S g o.keys.rk ∧ FreshSafeTerm compI0 S g o.keys.ck ∧
    FreshSafeTerm compI0 S g o.keys.pqr := by
  have hkdf := freshSafeTerm_pqxdhKdf_none
    (freshSafeTerm_dh hspk_key hikA) (freshSafeTerm_dh hikB_key hek)
    (freshSafeTerm_dh hspk_key hek) (freshSafeTerm_kemEncap_snd hpqpk hent)
  exact ⟨freshSafeTerm_dhPk hikA, hikB, hspk, hpqpk, freshSafeTerm_dhPk hek, freshSafeTerm_kemEncap_fst hpqpk hent, hkdf.1, hkdf.2.1, hkdf.2.2⟩
theorem freshSafeTerm_iniAliceStartState {S : Sem} {g : Ghost} {tr₁ : ExecTrace} {b : Participant} {ikA ikB spk pqpk : DY.Bytes} (hikA : FreshSafeTerm compI0 S g ikA) (hikB : FreshSafeTerm compI0 S g ikB) (hikB_key : FreshSafeTerm compI0 S g (DY.X25519.x25519Key ikB)) (hspk : FreshSafeTerm compI0 S g spk) (hspk_key : FreshSafeTerm compI0 S g (DY.X25519.x25519Key spk)) (hpqpk : FreshSafeTerm compI0 S g pqpk) (hek : FreshSafeTerm compI0 S g (randTerm tr₁.length 32)) (hent : FreshSafeTerm compI0 S g (randTerm (tr₁.length + 1) 32)) (hdhs : FreshSafeTerm compI0 S g (randTerm (tr₁.length + 2) 32)) : let o := iniAliceOut tr₁ ikA ikB spk pqpk none;
    let stA := iniAliceStartState tr₁ b o;
    FreshSafeTerm compI0 S g stA.myIk ∧ FreshSafeTerm compI0 S g stA.peerIk ∧ FreshSafeTerm compI0 S g stA.rk ∧ FreshSafeTerm compI0 S g stA.dhs ∧ FreshSafeTerm compI0 S g stA.cks ∧ FreshSafeTerm compI0 S g stA.sid ∧
    FreshSafeTerm compI0 S g stA.spqr := by
  have ho := freshSafeTerm_aliceOut hikA hikB hikB_key hspk hspk_key hpqpk hek hent; have hcc := freshSafeTerm_createChain ho.2.2.2.2.2.2.1 hspk_key hdhs
  exact ⟨freshSafeTerm_serializedIk compI0 S g ho.1, freshSafeTerm_serializedIk compI0 S g ho.2.1, hcc.1, hdhs, hcc.2, freshSafeTerm_sid hdhs ho.2.2.2.2.2.2.1,
         freshSafeTerm_spqrInit ho.2.2.2.2.2.2.2.2 (freshSafeTerm_lit_of_length_ne_64 compI0 S g _ (by decide))⟩
private theorem ver4_byte_ne_setupFresh {n : Nat} {t : Nat} (hn : n < 16) (ht : IsSetupFresh64Tag t) : BitVec.ofNat 8 (4 * 16 + n) ≠ BitVec.ofNat 8 t := by
  intro heq; have hval := congrArg BitVec.toNat heq
  simp only [BitVec.toNat_ofNat] at hval; rcases ht with rfl | rfl | rfl <;> omega
theorem freshSafeTerm_trWire_ver4 {i : ExternInterpretation} {S : Sem} {g : Ghost} {rk : DY.Bytes} {c pc : UInt32} {ct pq : DY.Bytes} {ev : DY.TrWire.EncodingVariation} (hrk : FreshSafeTerm i S g rk) (hct : FreshSafeTerm i S g ct) (hpq : FreshSafeTerm i S g pq) : FreshSafeTerm i S g (DY.TrWire.trWireMsg 4 rk c pc ct pq ev) := by
  refine freshSafeTerm_of_node (ts := [rk, ct, pq]) ?_
    (fun _ ht => ne_fillFresh64_of_head?_ne (b := BitVec.ofNat 8 (4 * 16 + ev.versionLowNibble % 16))
      (by rw [gamma_trWire_eq]; rfl) (ver4_byte_ne_setupFresh (Nat.mod_lt _ (by decide)) ht))
    (fun _ hu => (List.mem_cons.mp hu).elim (· ▸ hrk) (fun h =>
      (List.mem_cons.mp h).elim (· ▸ hct) (fun h => List.mem_singleton.mp h ▸ hpq)))
  unfold gamma'; dsimp only [DY.TrWire.trWireMsg, DY.TrWire.CanTrWireMsg.trWireMsg, DY.TrWire.instCanTrWireMsgBytes]; rw [DY.Bytes.rec_eq (gTrWire0 g) (gAll i S g)]; rfl
private theorem byte_ne_setupFresh4 {b : BitVec 8} {t : Nat} (hb11 : b ≠ 11#8) (hb16 : b ≠ 16#8) (hb17 : b ≠ 17#8) (ht : IsSetupFresh64Tag t) : b ≠ BitVec.ofNat 8 t := by rcases ht with rfl | rfl | rfl; exact hb11; exact hb16; exact hb17
theorem encMac_eq {tr₂ : ExecTrace} {stA : DY.Libsignal.TripleRatchet.TRState} {ikS ikR : DY.Bytes} (cl pq : Nat) (hmyIk : stA.myIk = DY.Libsignal.PQXDH.serializedIk ikS) (hpeerIk : stA.peerIk = DY.Libsignal.PQXDH.serializedIk ikR) : encMac tr₂ stA cl pq = DY.Libsignal.TripleRatchet.computeMac (DY.Libsignal.TripleRatchet.trMsgKeys (encSalt tr₂ stA cl pq) (DY.Libsignal.TripleRatchet.kdfCk stA.cks).2).macKey (DY.Libsignal.PQXDH.serializedIk ikS) (DY.Libsignal.PQXDH.serializedIk ikR) (DY.TrWire.trWireMsg 4 (DY.DiffieHellman.dhPk stA.dhs) stA.ns stA.pn (DY.SymEnc.symEnc (DY.Libsignal.TripleRatchet.trMsgKeys (encSalt tr₂ stA cl pq) (DY.Libsignal.TripleRatchet.kdfCk stA.cks).2).cipherKey (DY.Libsignal.TripleRatchet.trMsgKeys (encSalt tr₂ stA cl pq) (DY.Libsignal.TripleRatchet.kdfCk stA.cks).2).iv (randTerm tr₂.length 32)) (DY.Spqr.spqrSend stA.spqr (randTerm (tr₂.length + 1) cl)).2.2 DY.TrWire.canonicalVariation) := by unfold encMac; dsimp only; rw [hmyIk, hpeerIk]; rfl
theorem freshSafeTerm_encTerms {S : Sem} {g : Ghost} {tr₂ : ExecTrace} {stA : DY.Libsignal.TripleRatchet.TRState} {ikS ikR : DY.Bytes} {cl : Nat} (hmyIk : stA.myIk = DY.Libsignal.PQXDH.serializedIk ikS) (hpeerIk : stA.peerIk = DY.Libsignal.PQXDH.serializedIk ikR) (hikS : FreshSafeTerm compI0 S g ikS) (hikR : FreshSafeTerm compI0 S g ikR) (hdhs : FreshSafeTerm compI0 S g stA.dhs) (hcks : FreshSafeTerm compI0 S g stA.cks) (hspqr : FreshSafeTerm compI0 S g stA.spqr) (hm : FreshSafeTerm compI0 S g (randTerm tr₂.length 32)) (hm_len : (g.σ tr₂.length 32).length ≠ 64) (hcoins : FreshSafeTerm compI0 S g (randTerm (tr₂.length + 1) cl)) : let pq := tr₂.length + 2;
    let stA' := encSt tr₂ stA cl;
    FreshSafeTerm compI0 S g (encSalt tr₂ stA cl pq) ∧ FreshSafeTerm compI0 S g (encWire tr₂ stA cl pq) ∧ FreshSafeTerm compI0 S g (encMac tr₂ stA cl pq) ∧ FreshSafeTerm compI0 S g (encOut tr₂ stA cl pq) ∧ FreshSafeTerm compI0 S g stA'.cks ∧
    FreshSafeTerm compI0 S g stA'.spqr := by
  have hsalt : FreshSafeTerm compI0 S g (encSalt tr₂ stA cl (tr₂.length + 2)) := Eq.mp (congrArg (FreshSafeTerm compI0 S g) (encSalt_self tr₂ stA cl).symm)
      (freshSafeTerm_spqrSendKey hspqr hcoins)
  have hmk := freshSafeTerm_trMsgKeys hsalt hcks
  have hm_gamma_len : (gamma compI0 S g (randTerm tr₂.length 32)).length ≠ 64 :=
    Eq.mp (congrArg (fun l => l.length ≠ 64)
      (gamma_randTerm_eq_of_ne_zero compI0 S g tr₂.length 32 (by decide)).symm) hm_len
  have hct_msg := freshSafeTerm_symEnc hm_gamma_len hmk.1 hmk.2.2 hm; have hpq_msg := freshSafeTerm_spqrSendMsg hspqr hcoins; have hdhPk_dhs := freshSafeTerm_dhPk hdhs
  have hwire₀ := freshSafeTerm_trWire_ver4 (c := stA.ns) (pc := stA.pn)
    (ev := DY.TrWire.canonicalVariation) hdhPk_dhs hct_msg hpq_msg
  have hmac : FreshSafeTerm compI0 S g (encMac tr₂ stA cl (tr₂.length + 2)) := Eq.mp (congrArg (FreshSafeTerm compI0 S g) (encMac_eq cl (tr₂.length + 2) hmyIk hpeerIk).symm)
      (freshSafeTerm_trunc8 (freshSafeTerm_hmac hmk.2.1 (freshSafeTerm_concat
        (fun _ ht => gamma_concat_head?_ne_fillFresh64 compI0 S g (gamma_serializedIk_head? compI0 S g ikS)
          (byte_ne_setupFresh4 (by decide) (by decide) (by decide) ht))
        (freshSafeTerm_serializedIk compI0 S g hikS)
        (freshSafeTerm_concat
          (fun _ ht => gamma_concat_head?_ne_fillFresh64 compI0 S g (gamma_serializedIk_head? compI0 S g ikR)
            (byte_ne_setupFresh4 (by decide) (by decide) (by decide) ht))
          (freshSafeTerm_serializedIk compI0 S g hikR) hwire₀))))
  refine ⟨hsalt, hwire₀, hmac, freshSafeTerm_concat (fun _ ht => ?_) hwire₀ hmac, (freshSafeTerm_kdfCk hcks).1, freshSafeTerm_spqrSendState hspqr hcoins⟩
  exact gamma_concat_head?_ne_fillFresh64 compI0 S g (b0 := BitVec.ofNat 8 (4 * 16 + DY.TrWire.canonicalVariation.versionLowNibble % 16))
    (by change (gamma compI0 S g (DY.TrWire.trWireMsg 4 _ _ _ _ _ _)).head? = _; rw [gamma_trWire_eq]; rfl)
    (ver4_byte_ne_setupFresh (Nat.mod_lt _ (by decide)) ht)
theorem ofByteArray_length (b : ByteArray) : (ofByteArray b).length = b.size := by unfold ofByteArray ByteArray.size; simp
theorem freshSafeTerm_concatPrefixes_of_suffix_gt_64 {i : ExternInterpretation} {S : Sem} {g : Ghost} {ps : List DY.Bytes} {s : DY.Bytes} (hps : ∀ p ∈ ps, FreshSafeTerm i S g p) (hs : FreshSafeTerm i S g s) (hlen : 64 < (gamma i S g s).length) : FreshSafeTerm i S g (Comparse.concatPrefixes ps s) := by
  intro x hx t ht hval
  rcases mem_memo_concatPrefixes ps s hx with ⟨p, hp, hxp⟩ | hxs | ⟨_, hge⟩
  · exact hps p hp x hxp t ht hval
  · exact hs x hxs t ht hval
  · have h64 : x.2.2.length = 64 := by rw [hval, fillFresh_length t 64 (by decide)]
    omega
private theorem subtype_size_ne_64 {k : Nat} (x : { b : ByteArray // b.size = k }) (hk : k ≠ 64) : x.val.size ≠ 64 := by rw [x.property]; exact hk
theorem freshSafeTerm_mem_bool (i : ExternInterpretation) (S : Sem) (g : Ghost) (b : Bool) {p : DY.Bytes} (hp : p ∈ Comparse.NonExtensibleMessageFormat.bool.serialize b) : FreshSafeTerm i S g p := by
  obtain ⟨ba, hsz, hser⟩ := bool_serialize_singleton b
  rw [hser, List.mem_singleton] at hp; subst hp
  refine freshSafeTerm_lit_of_length_ne_64 i S g ba ?_; rw [ofByteArray_length, hsz]; decide
theorem freshSafeTerm_mem_slowNat (i : ExternInterpretation) (S : Sem) (g : Ghost) : ∀ (n : Nat) {p : DY.Bytes}, p ∈ Comparse.NonExtensibleMessageFormat.slowNat.serialize n → FreshSafeTerm i S g p
  | 0, _, hp => by
    rw [slowNat_serialize_zero] at hp
    exact freshSafeTerm_mem_bool i S g false hp
  | n + 1, _, hp => by
    rw [slowNat_serialize_succ n, List.mem_append] at hp
    exact hp.elim (freshSafeTerm_mem_bool i S g true) (freshSafeTerm_mem_slowNat i S g n)
theorem freshSafeTerm_mem_uint32 (i : ExternInterpretation) (S : Sem) (g : Ghost) (n : UInt32) {p : DY.Bytes} (hp : p ∈ Comparse.NonExtensibleMessageFormat.uint32.serialize n) : FreshSafeTerm i S g p := by
  obtain ⟨ba, hsz, hser⟩ := uint32_serialize_singleton n
  rw [hser, List.mem_singleton] at hp; subst hp
  refine freshSafeTerm_lit_of_length_ne_64 i S g ba ?_; rw [ofByteArray_length, hsz]; decide
theorem freshSafeTerm_mem_slowBytes {i : ExternInterpretation} {S : Sem} {g : Ghost} {b : DY.Bytes} (hb : FreshSafeTerm i S g b) {p : DY.Bytes} (hp : p ∈ Comparse.NonExtensibleMessageFormat.slowBytes.serialize b) : FreshSafeTerm i S g p := by
  rw [slowBytes_serialize_eq b, List.mem_append, List.mem_singleton] at hp
  exact hp.elim (freshSafeTerm_mem_slowNat i S g _) (· ▸ hb)
theorem freshSafeTerm_mem_slowString (i : ExternInterpretation) (S : Sem) (g : Ghost) {s : String} (hs : s.toUTF8.size ≠ 64) {p : DY.Bytes} (hp : p ∈ Comparse.NonExtensibleMessageFormat.slowString.serialize s) : FreshSafeTerm i S g p := by
  rw [slowString_serialize_eq s, List.mem_append, List.mem_singleton] at hp
  rcases hp with hnat | rfl
  · exact freshSafeTerm_mem_slowNat i S g _ hnat
  · refine freshSafeTerm_lit_of_length_ne_64 i S g s.toUTF8 ?_; rw [ofByteArray_length]; exact hs
theorem gamma_literalToBytes_length (i : ExternInterpretation) (S : Sem) (g : Ghost) (b : ByteArray) : (gamma i S g (DY.Literal.literalToBytes b)).length = b.size := by change (gamma i S g (({ lit := b } : DY.Literal.Literal.SubF DY.Bytes).pack)).length = b.size; rw [gamma_lit, ofByteArray_length]
theorem gamma_bool_serialize_length (i : ExternInterpretation) (S : Sem) (g : Ghost) (b : Bool) : ((Comparse.NonExtensibleMessageFormat.bool.serialize b).flatMap (gamma i S g)).length = 1 := by
  obtain ⟨ba, hsz, hser⟩ := bool_serialize_singleton b
  rw [hser]; change (gamma i S g (DY.Literal.literalToBytes ba) ++ []).length = 1
  rw [List.append_nil, gamma_literalToBytes_length, hsz]
theorem gamma_slowNat_serialize_length (i : ExternInterpretation) (S : Sem) (g : Ghost) : ∀ (n : Nat), ((Comparse.NonExtensibleMessageFormat.slowNat.serialize n).flatMap (gamma i S g)).length = n + 1
  | 0 => by rw [slowNat_serialize_zero]; exact gamma_bool_serialize_length i S g false
  | n + 1 => by
    rw [slowNat_serialize_succ n, List.flatMap_append, List.length_append, gamma_bool_serialize_length i S g true, gamma_slowNat_serialize_length i S g n]; omega
theorem gamma_uint32_serialize_length (i : ExternInterpretation) (S : Sem) (g : Ghost) (n : UInt32) : ((Comparse.NonExtensibleMessageFormat.uint32.serialize n).flatMap (gamma i S g)).length = 4 := by
  obtain ⟨ba, hsz, hser⟩ := uint32_serialize_singleton n
  rw [hser]; change (gamma i S g (DY.Literal.literalToBytes ba) ++ []).length = 4
  rw [List.append_nil, gamma_literalToBytes_length, hsz]
theorem append_mid32_ne_fillFresh64 {A B C : HwBytes} (t : Nat) (hA : 1 ≤ A.length) (hB_len : B.length = 32) (hB_ne : B ≠ List.replicate 32 0#8) : A ++ (B ++ C) ≠ fillFresh t 64 := by
  intro heq; have hlen : (A ++ (B ++ C)).length = (fillFresh t 64).length := congrArg List.length heq; rw [List.length_append, List.length_append, hB_len, fillFresh64_length] at hlen; have hslice := congrArg (fun l => (l.drop A.length).take 32) heq; rw [List.drop_left, List.take_left' hB_len] at hslice; obtain ⟨k, hk⟩ : ∃ k, A.length = k + 1 := ⟨A.length - 1, by omega⟩; have hff : fillFresh t 64 = BitVec.ofNat 8 t :: List.replicate 63 0#8 := rfl
  rw [hk, hff, List.drop_succ_cons, List.drop_replicate,
    List.take_replicate, Nat.min_eq_left (by omega)] at hslice
  exact hB_ne hslice
theorem freshSafeTerm_concatPrefixes_of_length_lt_64 {i : ExternInterpretation} {S : Sem} {g : Ghost} : ∀ (ps : List DY.Bytes) {s : DY.Bytes}, (∀ p ∈ ps, FreshSafeTerm i S g p) → FreshSafeTerm i S g s → (gamma i S g (Comparse.concatPrefixes ps s)).length < 64 → FreshSafeTerm i S g (Comparse.concatPrefixes ps s)
  | [], s, _, hs, _ => by rw [concatPrefixes_nil]; exact hs
  | p :: ps, s, hps, hs, hlen => by
    have hstep := gamma_concat_eq i S g p (Comparse.concatPrefixes ps s); have hlen' : (gamma i S g (Comparse.concatPrefixes ps s)).length < 64 := (by have h := hlen; rw [concatPrefixes_cons, hstep, List.length_append] at h; omega)
    rw [concatPrefixes_cons]
    refine freshSafeTerm_concat (fun _ _ => ne_fillFresh64_of_length_ne ?_) (hps p List.mem_cons_self) (freshSafeTerm_concatPrefixes_of_length_lt_64 ps
        (fun q hq => hps q (List.mem_cons_of_mem p hq)) hs hlen')
    rw [← concatPrefixes_cons]; omega
theorem freshSafeTerm_concatPrefixes_slowNat_mid32 {i : ExternInterpretation} {S : Sem} {g : Ghost} {b s : DY.Bytes} (hb_len : (gamma i S g b).length = 32) (hb_ne : gamma i S g b ≠ List.replicate 32 0#8) (hbs : FreshSafeTerm i S g (DY.Concat.concat b s)) : ∀ (n : Nat), FreshSafeTerm i S g (Comparse.concatPrefixes (Comparse.NonExtensibleMessageFormat.slowNat.serialize n) (DY.Concat.concat b s))
  | 0 => by
    have h0 := slowNat_serialize_zero
    obtain ⟨ba₀, _, hp₀⟩ := bool_serialize_singleton false
    let p₀ : DY.Bytes := DY.Literal.literalToBytes ba₀
    have hp₀' : (Comparse.NonExtensibleMessageFormat.bool (Bytes := DY.Bytes)).serialize false = [p₀] := hp₀
    have hp₀_mem : p₀ ∈ (Comparse.NonExtensibleMessageFormat.bool (Bytes := DY.Bytes)).serialize false := by rw [hp₀']; exact List.mem_cons_self
    have hlen_p₀ : (gamma i S g p₀).length = 1 := (by have h := gamma_bool_serialize_length i S g false; rw [hp₀', List.flatMap_cons, List.flatMap_nil, List.append_nil] at h; exact h); rw [h0, hp₀', concatPrefixes_cons, concatPrefixes_nil]; refine freshSafeTerm_concat ?_ (freshSafeTerm_mem_bool i S g false hp₀_mem) hbs; intro t _; rw [gamma_concat_eq, gamma_concat_eq]; exact append_mid32_ne_fillFresh64 t (by omega) hb_len hb_ne
  | n + 1 => by
    have hstep := slowNat_serialize_succ n
    obtain ⟨ba₁, _, hp₁⟩ := bool_serialize_singleton true
    let p₁ : DY.Bytes := DY.Literal.literalToBytes ba₁
    have hp₁' : (Comparse.NonExtensibleMessageFormat.bool (Bytes := DY.Bytes)).serialize true = [p₁] := hp₁
    have hp₁_mem : p₁ ∈ (Comparse.NonExtensibleMessageFormat.bool (Bytes := DY.Bytes)).serialize true := by rw [hp₁']; exact List.mem_cons_self
    have heq_cat :
        DY.Concat.concat p₁ (Comparse.concatPrefixes (Comparse.NonExtensibleMessageFormat.slowNat.serialize n) (DY.Concat.concat b s)) = Comparse.concatPrefixes (Comparse.NonExtensibleMessageFormat.slowNat.serialize (n + 1))
          (DY.Concat.concat b s) := by rw [hstep, ← concatPrefixes_append, hp₁', concatPrefixes_cons, concatPrefixes_nil]
    rw [← heq_cat]; refine freshSafeTerm_concat ?_ (freshSafeTerm_mem_bool i S g true hp₁_mem) (freshSafeTerm_concatPrefixes_slowNat_mid32 hb_len hb_ne hbs n); intro t _; rw [heq_cat, gamma_concatPrefixes, gamma_concat_eq]; have hlen_nat := gamma_slowNat_serialize_length i S g (n + 1); exact append_mid32_ne_fillFresh64 t (by omega) hb_len hb_ne
theorem freshSafeTerm_concatPrefixes_slowBytes_mid32 {i : ExternInterpretation} {S : Sem} {g : Ghost} {b s : DY.Bytes} (hb : FreshSafeTerm i S g b) (hs : FreshSafeTerm i S g s) (hb_len : (gamma i S g b).length = 32) (hb_ne : gamma i S g b ≠ List.replicate 32 0#8) (hlen : (gamma i S g b).length + (gamma i S g s).length ≠ 64) : FreshSafeTerm i S g (Comparse.concatPrefixes (Comparse.NonExtensibleMessageFormat.slowBytes.serialize b) s) := by have hser := slowBytes_serialize_eq b; rw [hser, ← concatPrefixes_append, concatPrefixes_cons, concatPrefixes_nil]; refine freshSafeTerm_concatPrefixes_slowNat_mid32 hb_len hb_ne ?_ (Comparse.BytesLike.length b); refine freshSafeTerm_concat (fun _ _ => ne_fillFresh64_of_length_ne ?_) hb hs; rw [gamma_concat_eq, List.length_append]; exact hlen
theorem freshSafeTerm_mem_trStatePrefixes {S : Sem} {g : Ghost} {ls : DY.PersistentLocalState.LocalState DY.Libsignal.TripleRatchet.TRState} (hpart : ls.participant.toUTF8.size ≠ 64) (hpeer : ls.state.peer.toUTF8.size ≠ 64) (hmyIk : FreshSafeTerm compI0 S g ls.state.myIk) (hpeerIk : FreshSafeTerm compI0 S g ls.state.peerIk) (hrk : FreshSafeTerm compI0 S g ls.state.rk) (hdhs : FreshSafeTerm compI0 S g ls.state.dhs) (hcks : FreshSafeTerm compI0 S g ls.state.cks) (hsid : FreshSafeTerm compI0 S g ls.state.sid) (hspqr : FreshSafeTerm compI0 S g ls.state.spqr) {p : DY.Bytes} (hp : p ∈ trStatePrefixes ls) : FreshSafeTerm compI0 S g p := by
  unfold trStatePrefixes at hp; simp only [List.mem_append] at hp
  rcases hp with h | h | h | h | h | h | h | h | h | h | h | h | h
  exacts [freshSafeTerm_mem_slowString compI0 S g hpart h, freshSafeTerm_mem_slowString compI0 S g hpeer h, freshSafeTerm_mem_slowBytes hmyIk h, freshSafeTerm_mem_slowBytes hpeerIk h, freshSafeTerm_mem_slowBytes hrk h, freshSafeTerm_mem_slowBytes hdhs h, freshSafeTerm_mem_slowBytes hcks h, freshSafeTerm_mem_uint32 compI0 S g _ h, freshSafeTerm_mem_uint32 compI0 S g _ h, freshSafeTerm_mem_slowBytes hsid h, freshSafeTerm_mem_bool compI0 S g _ h, freshSafeTerm_mem_slowNat compI0 S g _ h, freshSafeTerm_mem_slowBytes hspqr h]
end Symbolic.BugInjection.Proofs.Common443.CompPrefixInvFresh
