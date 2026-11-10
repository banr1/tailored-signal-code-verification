/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common.CompFitsSatisfiable
public import Symbolic.BugInjection.Proofs.Common443.CliCoinSplit
public import Symbolic.BugInjection.Proofs.Common443.Census443Close
public import Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupHighBitComp443.NoBsc
public import Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupTorsionComp443.NoBsc

/-!
# CLI Coin-Split and Wrap-Swap Helpers for Small-Subgroup Proofs

Proves that swapping wrapped pre-key handles in `Move.encrypt` preserves `ExplainsCli`, and lifts
`BobStartCollision` refutations and initial coin-split equalities to the high-bit and torsion
small-subgroup CLI witnesses.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
cref_hide_foreign_instances

abbrev DY.Libsignal.Composed.Refinement.Cli.CallsFit := DY.Libsignal.Composed.Refinement.Cli.CallsMatchSchedules
abbrev DY.Libsignal.Composed.Refinement.Cli.HooksAgree := DY.Libsignal.Composed.Refinement.Cli.HooksMatchInterpretation
abbrev DY.Libsignal.Composed.Refinement.Cli.CollisionAtCli := DY.Libsignal.Composed.Refinement.Cli.CollisionAfterExplainedPrefixMoves

namespace Symbolic.BugInjection.Proofs.Common443.CliCoinSplitClose

open ByteSpecs
open DY DY.Libsignal.Composed DY.Libsignal.Composed.Refinement DY.Libsignal.Composed.Refinement.Cli DY.Libsignal.HwEvents
open DY.Libsignal (HwBytes)
open CryptoProofLib.Refinement (ExternInterpretation)
open Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompTrace
open Symbolic.BugInjection.Proofs.Common443.CompPrefixInvSwap
open Symbolic.BugInjection.Proofs.Common443.CliCoinSplit
open Symbolic.BugInjection.Proofs.Common443.Census443Close

theorem not_rng_of_mem_encSend (tr tr' : ExecTrace) (w : Option (Nat × Nat))
    {v : VisEntry} (hv : v ∈ encSend tr tr' w) : v.kind ≠ .rng := by
  unfold encSend at hv
  rcases h1 : lastSent tr tr' with _ | msg <;> rcases w with _ | ⟨e, c⟩ <;>
    simp [h1] at hv <;> subst hv <;> intro h <;> cases h

theorem encrypt_vis_mem_of_rng (tr : ExecTrace) (me : Participant) (s cl pq : Nat)
    (w₁ w₂ : Option (Nat × Nat)) {v : VisEntry}
    (hv : v ∈ (Move.encrypt me s cl pq w₂).vis tr) (hk : v.kind = .rng) :
    v ∈ (Move.encrypt me s cl pq w₁).vis tr := by
  simp only [Move.vis, encrypt_next_eq_wrap tr me s cl pq w₂ w₁, encVis, ↓reduceIte,
    List.mem_append] at hv ⊢
  rcases hv with (hv | hv) | hv
  · exact Or.inl (Or.inl hv)
  · exact absurd hk (not_rng_of_mem_encSend tr ((Move.encrypt me s cl pq w₁).next tr) w₂ hv)
  · exact Or.inr hv

theorem any_eq_of_map_kind_eq {vs₁ vs₂ : List VisEntry} (p : Kind → Bool)
    (h : vs₁.map VisEntry.kind = vs₂.map VisEntry.kind) :
    vs₁.any (fun v => p v.kind) = vs₂.any (fun v => p v.kind) := by
  have h1 : ∀ vs : List VisEntry, vs.any (fun v => p v.kind) = (vs.map VisEntry.kind).any p := by
    intro vs
    rw [List.any_map]
    rfl
  rw [h1 vs₁, h1 vs₂, h]

theorem encrypt_vis_any_kind_eq (tr : ExecTrace) (me : Participant) (s cl pq : Nat)
    (w₁ w₂ : Option (Nat × Nat)) (p : Kind → Bool) :
    ((Move.encrypt me s cl pq w₂).vis tr).any (fun v => p v.kind) =
    ((Move.encrypt me s cl pq w₁).vis tr).any (fun v => p v.kind) :=
  any_eq_of_map_kind_eq p (encrypt_vis_map_kind tr me s cl pq w₂ w₁)

theorem outcomeFaithfulCli_set_wrap {r : Records} {ok : Nat → Bool} {ms : List Move}
    {k : Nat} {me : Participant} {s cl pq : Nat} {w₁ w₂ : Option (Nat × Nat)}
    (hk : ms[k]? = some (.encrypt me s cl pq w₁))
    (hout : OutcomeFaithfulCli r ok ms) :
    OutcomeFaithfulCli r ok (ms.set k (.encrypt me s cl pq w₂)) := by
  refine ⟨outcomeFaithful_set_wrap hk hout.1, ?_⟩
  intro idx m' hm'
  dsimp only
  intro hgate' hok'
  rw [runTrace_take_set_wrap hk idx] at hgate' ⊢
  rw [callCount_runVis_take_set_wrap hk idx] at hok'
  obtain ⟨m, hm, _, _, _, _, hnext, _⟩ := getElem?_set_encrypt_props hk hm'
  rw [hnext]
  by_cases hidx : idx = k
  · subst hidx
    rw [List.getElem?_set_self (by obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp hk; exact hlt)] at hm'
    injection hm' with hm'_eq
    subst hm'_eq
    have hmeq : m = .encrypt me s cl pq w₁ := Option.some.inj (hm.symm.trans hk)
    subst hmeq
    have h1 := encrypt_vis_any_kind_eq (runTraceMoves r (ms.take idx)) me s cl pq w₁ w₂
      (fun kd => kd == Kind.recv || kd == Kind.pt)
    have h2 := encrypt_vis_any_kind_eq (runTraceMoves r (ms.take idx)) me s cl pq w₁ w₂
      (fun kd => kd == Kind.send || kd == Kind.accept)
    rw [h1] at hgate'
    rw [h2]
    exact hout.2 idx (.encrypt me s cl pq w₁) hk hgate' hok'
  · rw [List.getElem?_set_ne (Ne.symm hidx)] at hm'
    have hmeq : m' = m := Option.some.inj (hm'.symm.trans hm)
    subst hmeq
    exact hout.2 idx m' hm hgate' hok'

theorem rngLengthsFaithfulCli_set_wrap {i : ExternInterpretation} {r : Records} {S : Sem}
    {g : Ghost} {ms : List Move}
    {k : Nat} {me : Participant} {s cl pq : Nat} {w₁ w₂ : Option (Nat × Nat)}
    (hk : ms[k]? = some (.encrypt me s cl pq w₁))
    (hrng : RngLengthsFaithfulCli i r S g ms) :
    RngLengthsFaithfulCli i r S g (ms.set k (.encrypt me s cl pq w₂)) := by
  intro idx m' hm'
  dsimp only
  rw [runTrace_take_set_wrap hk idx]
  by_cases hidx : idx = k
  · subst hidx
    rw [List.getElem?_set_self (by obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp hk; exact hlt)] at hm'
    injection hm' with hm'_eq
    subst hm'_eq
    have h1 := encrypt_vis_any_kind_eq (runTraceMoves r (ms.take idx)) me s cl pq w₁ w₂
      (fun kd => kd == Kind.recv)
    rw [h1]
    intro hrecv v t hv hvk
    exact hrng idx (.encrypt me s cl pq w₁) hk hrecv v t
      (encrypt_vis_mem_of_rng _ me s cl pq w₁ w₂ hv hvk) hvk
  · rw [List.getElem?_set_ne (Ne.symm hidx)] at hm'
    exact hrng idx m' hm'

theorem explainsCli_set_wrap {i : ExternInterpretation} {r : Records} {S : Sem}
    {who : List Participant} {ok : Nat → Bool} {σ₁ τ₁ : List MachineEvent} {g : Ghost} {ms : List Move}
    {k : Nat} {me : Participant} {s cl pq e c e' c' : Nat}
    (hk : ms[k]? = some (.encrypt me s cl pq (some (e, c))))
    (hγ : (received (runTraceMoves r (ms.take k)) [e, c]).map (gamma i S g) =
          (received (runTraceMoves r (ms.take k)) [e', c']).map (gamma i S g))
    (hex : ExplainsCli i r S who ok σ₁ τ₁ g ms) :
    ExplainsCli i r S who ok σ₁ τ₁ g (ms.set k (.encrypt me s cl pq (some (e', c')))) := by
  rcases hex with ⟨hcs, hmp, hout, hrng⟩
  exact ⟨hcs, matchedPrefix_set_wrap hk hγ hmp,
    outcomeFaithfulCli_set_wrap hk hout,
    rngLengthsFaithfulCli_set_wrap hk hrng⟩

theorem explainsCli_of_explains_mid_encrypt_swap {i : ExternInterpretation} {r : Records} {S : Sem}
    {who : List Participant} {ok : Nat → Bool} {σ₁ τ₁ : List MachineEvent} {g : Ghost}
    {pre mid post : List Move} {m₀ : Move} {me : Participant} {s cl pq : Nat} {w₁ w₂ : Option (Nat × Nat)}
    (hex_cli : ExplainsCli i r S who ok σ₁ τ₁ g (pre ++ m₀ :: mid ++ .encrypt me s cl pq w₁ :: post))
    (hex' : DY.Libsignal.Composed.Refinement.ExplainsMoves i r S who ok g
      (pre ++ m₀ :: mid ++ .encrypt me s cl pq w₂ :: post) τ₁) :
    ExplainsCli i r S who ok σ₁ τ₁ g (pre ++ m₀ :: mid ++ .encrypt me s cl pq w₂ :: post) := by
  have hk : (pre ++ m₀ :: mid ++ Move.encrypt me s cl pq w₁ :: post)[(pre ++ m₀ :: mid).length]? =
      some (.encrypt me s cl pq w₁) := by
    rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]; rfl
  have hset : (pre ++ m₀ :: mid ++ Move.encrypt me s cl pq w₁ :: post).set
      (pre ++ m₀ :: mid).length (.encrypt me s cl pq w₂) =
      pre ++ m₀ :: mid ++ Move.encrypt me s cl pq w₂ :: post := by
    rw [List.set_append_right _ _ (Nat.le_refl _), Nat.sub_self]; rfl
  rcases hex_cli with ⟨hcs, _, hout, hrng⟩
  have hout' := outcomeFaithfulCli_set_wrap (w₂ := w₂) hk hout
  have hrng' := rngLengthsFaithfulCli_set_wrap (w₂ := w₂) hk hrng
  rw [hset] at hout' hrng'
  exact ⟨hcs, hex'.1, hout', hrng'⟩

open DY.Libsignal.PQXDH.Refinement (kyberEncapsSymbol)
open Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0
open CompFreshDistinct CompPrefixInvAlice CompPrefixInvBundle CompPrefixInvEnc CompPrefixInvStruct
open CompRNoBSC CompRPlantWire CompRFaithfulInner CompRX0SS38 CompRX0NBSC38 CompRX0NBSC38Hmc CompRX0NBSC38Parts CompRX0Top CompRX0Gamma CompRX0Mem CompRTag CompRNbsc38VT

attribute [local irreducible] Symbolic.BugInjection.hexBytes

theorem split38_decomp_swap_rep_cli {r : Records} {S : Sem} {who : List Participant} {ok : Nat → Bool}
    {g : Ghost} {ms : List Move} {σ₁ τ₁ rs' blk₁ : List MachineEvent} {bun b₀ pt c w b : HwBytes}
    {p q₀ : PreKeyFields} (v : Fin 4) (t : Fin 8) (hNe : r.alice ≠ r.bob)
    (hnb : CompSetupSecrecy.NoBrk r ms)
    (hEq : DY.Libsignal.Refinement.CryptoEquationsHold compI0)
    (hs1 : compSecretIdx (clamp (secretBytes r 1)) = some ⟨4, by decide⟩)
    (hs2 : compSecretIdx (clamp (secretBytes r 2)) = some ⟨3, by decide⟩)
    (hcs : Cli.CoinSplit [.pt pt, .rng c, .send w] blk₁)
    (hτ₁ : τ₁ = (.recv bun :: .rng b₀ :: rs') ++ blk₁)
    (hrs_len : rs'.length = 33)
    (hrs_kind : ∀ e ∈ (MachineEvent.rng b₀ :: rs'), eventKind e = .rng)
    (hbun4 : bun[4]? ≠ some 1#8)
    (hw : w.head? ≠ some DY.Libsignal.TripleRatchet.Refinement.wireWhisperTag)
    (hw4 : CompRBobInit.hasTag4 w = false)
    (hlen : w.length < 2 ^ 63) (hq₀ : parsePreKeyWire w = some q₀)
    (hbk₀ : q₀.baseKey = ecKey (compLookupPub (clamp b₀)))
    (hkc₀ : Compat compI0 r S g → q₀.kyberCiphertext = some (kyberKey (((compI0 kyberEncapsSymbol [gamma compI0 S g (setupPublic r 6), coinHeads (rs'.take 32)]).getD []).take 1568)))
    (hp : parsePreKeyWire b = some p)
    (hbk : ∀ k : DY.Bytes, DY.X25519.x25519Key k = k → gamma compI0 S g k = compLookupPub (clamp b₀) → p.baseKey.take 33 = ecKey (gamma compI0 S g (DY.X25519.x25519TorsionVariant k v t)))
    (hkc : p.kyberCiphertext = q₀.kyberCiphertext)
    (hpm : p.message = q₀.message)
    (hcan : InnerWireCanonical p)
    (hout : CompRPreKeyWire.PreKeyOuterMatches compI0 r b p)
    (hkvar : ∀ (tr : ExecTrace) (k : DY.Bytes), DY.X25519.x25519Key k = k → k.AttackerKnows tr → (DY.X25519.x25519TorsionVariant k v t).AttackerKnows tr)
    (hex_cli : ExplainsCli compI0 r S who ok σ₁ τ₁ g ms) :
    ∃ (pre mid post : List Move) (hb : DY.Libsignal.PQXDH.BundleHandles) (shown cl e c' : Nat),
      let tr₁ := (runMoves pre (setupTrace r)).1
      let o := aliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none
      let m₀ := Move.aliceStart r.alice r.bob 4 6 hb shown
      let tr₂ := (runMoves mid (m₀.next tr₁)).1
      let stA := aliceStartState tr₁ r.bob o
      let ms₀ := pre ++ m₀ :: mid ++ .encrypt r.alice (tr₁.length + 8) cl (tr₂.length + 2) (some (e, c')) :: post
      let ms' := pre ++ m₀ :: mid ++ .encrypt r.alice (tr₁.length + 8) cl (tr₂.length + 2) (some (tr₁.length + 3, tr₁.length + 4)) :: post
      let x₀ : PreKeyRep := ⟨DY.X25519.x25519TorsionVariant o.ek v t, o.ct, CompPrefixInvEnc.encOut tr₂ stA cl (tr₂.length + 2)⟩
      ms = ms₀ ∧ Compat compI0 r S g ∧ ModelRun r ms₀ ∧ List.Forall₂ (EventMatchesEntry compI0 r S g) τ₁ (runVis r ms₀) ∧
      Symbolic.Swarm.CREF.MovesFrom Symbolic.Swarm.CREF.InvisibleNoEffect (setupTrace r) pre ∧
      Symbolic.Swarm.CREF.MovesFrom Symbolic.Swarm.CREF.InvisibleNoEffect (m₀.next tr₁) mid ∧
      Symbolic.Swarm.CREF.MovesFrom Symbolic.Swarm.CREF.InvisibleNoEffect
        ((Move.encrypt r.alice (tr₁.length + 8) cl (tr₂.length + 2) (some (e, c'))).next tr₂) post ∧
      m₀.next tr₁ = aliceStartTrOfOut tr₁ r.alice r.bob o ∧
      bobDoneBaseKeys (runTraceMoves r ms₀) = [] ∧ ExplainsCli compI0 r S who ok σ₁ τ₁ g ms' ∧
      x₀ ∈ preKeyRepresentations compI0 r S g ms' b := by
  have hex : DY.Libsignal.Composed.Refinement.ExplainsMoves compI0 r S who ok g ms τ₁ := ⟨hex_cli.2.1, hex_cli.2.2.1.1⟩
  have hmp : DY.Libsignal.Composed.Refinement.MatchedPrefix compI0 r S who g ms
      ((.recv bun :: .rng b₀ :: rs') ++ blk₁) := hτ₁ ▸ hex.1
  obtain ⟨pre, a, idS, hb, shown, mid, cl, e, c', post, ikA, tr₁, tr₂, o, stA, htr₁, ho, hstA, htr₂, hms, hdisj, hek, hct, hekK, hctK, hencK, hnil, hvis₀, hsm, hm₀, hpre, hmid, hpost⟩ :=
    CliCoinSplit.pia_x0_decomp_split hNe hnb hcs hmp (by simp [hrs_len]) hrs_kind hbun4 hw
  have hc : Compat compI0 r S g := hex.1.1
  have hmr : ModelRun r ms := hex.1.2.1
  have hvis : List.Forall₂ (EventMatchesEntry compI0 r S g) τ₁ (runVis r ms) := hex.1.2.2.2.2.2
  rcases hdisj with ⟨hidS, ha, hikA⟩ | ⟨hidS, ha, hikA⟩
  · subst hidS ha hikA ho hstA htr₂ htr₁ hms; rw [hm₀] at hvis₀; obtain ⟨hγek, hγe⟩ := CompRX0Gamma.aliceVis_rng_coins hvis₀
    have hek_γ := CompRX0Gamma.gamma_iniAliceOut_ek_compI0 (S := S) (g := g)
      (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none hγek
    have hcoins : (coinHeads (rs'.take 32)).length = 32 := by simp [coinHeads, hrs_len]
    have hct_γ := CompRX0Gamma.gamma_iniAliceOut_ct (i := compI0) (S := S) (g := g)
      (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none
      (by rw [hγe]; exact hcoins)
    rw [hγe] at hct_γ
    obtain ⟨hex', hmem'⟩ := CompRX0Join.swap_and_mem_split38 (ek₀ := DY.X25519.x25519TorsionVariant (aliceOut (runMoves pre (setupTrace r)).1 (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none).ek v t)
      rfl rfl hek hct hsm rfl rfl hlen hq₀ (hek_γ ▸ hbk₀) (hct_γ ▸ hkc₀ hc) hp
      (hbk _ (CompPlant.x25519Key_dhPk _) hek_γ) hkc hpm hcan hout hex (hkvar _ _ (CompPlant.x25519Key_dhPk _) hekK) hctK hencK
    exact ⟨pre, mid, post, hb, shown, cl, e, c', rfl, hc, hmr, hvis, hpre, hmid, hpost, hm₀, hnil,
      explainsCli_of_explains_mid_encrypt_swap hex_cli hex', hmem'⟩
  · exfalso; subst hidS ha hikA ho hstA; obtain ⟨ek', ct', hL, -⟩ := sendMatches_append_inv hsm hlen hq₀; rw [hL] at hsm; exact CompRX0Bytes.not_sendMatches_bobSelf hNe hEq hc hs1 hs2 w hw4 tr₁ tr₂ r.bob _ _ ek' ct' cl _ hsm

theorem noBsc38HB_cli_swap {who : List Participant} {ok : Nat → Bool} {σ₁ blk₁ : List MachineEvent}
    (hcs : Cli.CoinSplit [.pt CompRX0SS38.ptB, .rng CompRX0SS38.cB, .send CompRPlantWire.sentWireBytes] blk₁)
    (r : Records) (S : Sem) (g : Ghost) (ms : List Move) (p : PreKeyFields)
    (hfits : compFitsPinned Symbolic.BugInjection.Witnesses.Cheval26SmallSubgroupHighBitComp.setup compI0 r)
    (hnb : CompSetupSecrecy.NoBrk r ms)
    (hex : ExplainsCli compI0 r S who ok σ₁
      ((.recv CompRX0SS38.bunBytes :: .rng CompRX0SS38.b0Bytes :: CompRX0SS38.rsT) ++ blk₁) g ms)
    (hp : parsePreKeyWire Census443Defs.highBitWireBytes = some p) :
    ∃ (pre mid post : List Move) (hb_eq : DY.Libsignal.PQXDH.BundleHandles) (shown cl e c' : Nat),
      let tr₁ := (runMoves pre (setupTrace r)).1
      let o := aliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none
      let m₀ := Move.aliceStart r.alice r.bob 4 6 hb_eq shown
      let tr₂ := (runMoves mid (m₀.next tr₁)).1
      let ms' := pre ++ m₀ :: mid ++ .encrypt r.alice (tr₁.length + 8) cl (tr₂.length + 2) (some (tr₁.length + 3, tr₁.length + 4)) :: post
      ms = pre ++ m₀ :: mid ++ .encrypt r.alice (tr₁.length + 8) cl (tr₂.length + 2) (some (e, c')) :: post ∧
      Symbolic.Swarm.CREF.MovesFrom Symbolic.Swarm.CREF.InvisibleNoEffect (setupTrace r) pre ∧
      Symbolic.Swarm.CREF.MovesFrom Symbolic.Swarm.CREF.InvisibleNoEffect (m₀.next tr₁) mid ∧
      Symbolic.Swarm.CREF.MovesFrom Symbolic.Swarm.CREF.InvisibleNoEffect
        ((Move.encrypt r.alice (tr₁.length + 8) cl (tr₂.length + 2) (some (e, c'))).next tr₂) post ∧
      m₀.next tr₁ = aliceStartTrOfOut tr₁ r.alice r.bob o ∧
      ExplainsCli compI0 r S who ok σ₁
        ((.recv CompRX0SS38.bunBytes :: .rng CompRX0SS38.b0Bytes :: CompRX0SS38.rsT) ++ blk₁) g ms' ∧
      ∃ x ∈ preKeyRepresentations compI0 r S g ms' Census443Defs.highBitWireBytes,
        ¬ BobStartCollision compI0 r S g ms' p x := by
  have hp' := hp
  rw [census_highBitWireBytes] at hp'
  rcases hfits.1 with ⟨hwf, -, -, -, -, -, -, hb, hs, -, -, -, -, hEq, -, -⟩
  have hs1 : compSecretIdx (clamp (secretBytes r 1)) = some ⟨4, by decide⟩ := by rw [hb]; exact highBitComp_compSecretIdx_bobId
  have hs2 : compSecretIdx (clamp (secretBytes r 2)) = some ⟨3, by decide⟩ := by rw [hs]; exact highBitComp_compSecretIdx_spk
  obtain ⟨q₀, hq₀, -⟩ := sentWireBytes_innerWireCanonical.1
  have hcan : InnerWireCanonical p := highBitWireBytes_innerWireCanonical.2 p hp'
  obtain ⟨hpbk, hkc, hpm, -, -⟩ := wirePairOk_spec wirePairOk_highBit hq₀ hp'
  obtain ⟨pre, mid, post, hb_eq, shown, cl, e, c', hms_eq, hc, hmr, hvis, hpre, hmid, hpost, hm₀, hnil, hex', hx₀⟩ :=
    split38_decomp_swap_rep_cli (v := 1) (t := 0) hwf.1 hnb hEq hs1 hs2 hcs rfl rsT_len rsT_kind bunBytes_getElem4_ne sentWireBytes_head_ne sentWireBytes_hasTag4 sentWireBytes_len hq₀ (sentWireBytes_baseKey hq₀)
      (fun _ => by rw [sentWireBytes_kyberCiphertext hq₀, compI0_kyberEncaps_rsT])
      hp'
      (fun k hk hγ => by
        rw [gamma_x25519TorsionVariant' S g k 1 0 (by decide), hk, hγ, clamp_b0_lookup]
        exact hpbk)
      hkc hpm hcan (outer_highBit hfits.1 hp') (CompRX0Split38.attackerKnows_torsionVariant 1 0) hex
  rw [← census_highBitWireBytes] at hx₀
  have hnbsc := nbscHighBitComp_split hcs compI0 r S hfits g p hp
  unfold Census443Defs.NBSC38' at hnbsc
  rw [census_iniAliceOut, census_iniAliceStartState, census_iniAliceStartTr, census_encOut] at hnbsc
  obtain ⟨hnb_pre, hnb_mid, hnb_post⟩ := CompRX0Top.noBrkTr_split38 (hms_eq ▸ hnb)
  exact ⟨pre, mid, post, hb_eq, shown, cl, e, c', hms_eq, hpre, hmid, hpost, hm₀, hex', _, hx₀,
    hnbsc pre mid post hb_eq shown cl e c' hc hmr hvis (CompRX0SS38.movesFrom_to_census443 hnb_pre hpre) (CompRX0SS38.movesFrom_to_census443 hnb_mid hmid) (CompRX0SS38.movesFrom_to_census443 hnb_post hpost) hm₀ hnil⟩

theorem noBsc38HB_cli {who : List Participant} {ok : Nat → Bool} {σ₁ blk₁ : List MachineEvent}
    (hcs : Cli.CoinSplit [.pt CompRX0SS38.ptB, .rng CompRX0SS38.cB, .send CompRPlantWire.sentWireBytes] blk₁)
    (r : Records) (S : Sem) (g : Ghost) (ms : List Move) (p : PreKeyFields)
    (hfits : compFitsPinned Symbolic.BugInjection.Witnesses.Cheval26SmallSubgroupHighBitComp.setup compI0 r)
    (hnb : CompSetupSecrecy.NoBrk r ms)
    (hex : ExplainsCli compI0 r S who ok σ₁
      ((.recv CompRX0SS38.bunBytes :: .rng CompRX0SS38.b0Bytes :: CompRX0SS38.rsT) ++ blk₁) g ms)
    (hp : parsePreKeyWire Census443Defs.highBitWireBytes = some p) :
    ∃ g' ms', ExplainsCli compI0 r S who ok σ₁
        ((.recv CompRX0SS38.bunBytes :: .rng CompRX0SS38.b0Bytes :: CompRX0SS38.rsT) ++ blk₁) g' ms' ∧
      ∃ x ∈ preKeyRepresentations compI0 r S g' ms' Census443Defs.highBitWireBytes,
        ¬ BobStartCollision compI0 r S g' ms' p x := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hex', x, hx, hnbsc⟩ :=
    noBsc38HB_cli_swap hcs r S g ms p hfits hnb hex hp
  exact ⟨g, _, hex', x, hx, hnbsc⟩

theorem noBsc38TC_cli_swap {who : List Participant} {ok : Nat → Bool} {σ₁ blk₁ : List MachineEvent}
    (hcs : Cli.CoinSplit [.pt CompRX0SS38.ptB, .rng CompRX0SS38.cB, .send CompRPlantWire.sentWireBytes] blk₁)
    (r : Records) (S : Sem) (g : Ghost) (ms : List Move) (p : PreKeyFields)
    (hfits : compFitsPinned Symbolic.BugInjection.Witnesses.Cheval26SmallSubgroupTorsionComp.setup compI0 r)
    (hnb : CompSetupSecrecy.NoBrk r ms)
    (hex : ExplainsCli compI0 r S who ok σ₁
      ((.recv CompRX0SS38.bunBytes :: .rng CompRX0SS38.b0Bytes :: CompRX0SS38.rsT) ++ blk₁) g ms)
    (hp : parsePreKeyWire Census443Defs.torsionWireBytes = some p) :
    ∃ (pre mid post : List Move) (hb_eq : DY.Libsignal.PQXDH.BundleHandles) (shown cl e c' : Nat),
      let tr₁ := (runMoves pre (setupTrace r)).1
      let o := aliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none
      let m₀ := Move.aliceStart r.alice r.bob 4 6 hb_eq shown
      let tr₂ := (runMoves mid (m₀.next tr₁)).1
      let ms' := pre ++ m₀ :: mid ++ .encrypt r.alice (tr₁.length + 8) cl (tr₂.length + 2) (some (tr₁.length + 3, tr₁.length + 4)) :: post
      ms = pre ++ m₀ :: mid ++ .encrypt r.alice (tr₁.length + 8) cl (tr₂.length + 2) (some (e, c')) :: post ∧
      Symbolic.Swarm.CREF.MovesFrom Symbolic.Swarm.CREF.InvisibleNoEffect (setupTrace r) pre ∧
      Symbolic.Swarm.CREF.MovesFrom Symbolic.Swarm.CREF.InvisibleNoEffect (m₀.next tr₁) mid ∧
      Symbolic.Swarm.CREF.MovesFrom Symbolic.Swarm.CREF.InvisibleNoEffect
        ((Move.encrypt r.alice (tr₁.length + 8) cl (tr₂.length + 2) (some (e, c'))).next tr₂) post ∧
      m₀.next tr₁ = aliceStartTrOfOut tr₁ r.alice r.bob o ∧
      ExplainsCli compI0 r S who ok σ₁
        ((.recv CompRX0SS38.bunBytes :: .rng CompRX0SS38.b0Bytes :: CompRX0SS38.rsT) ++ blk₁) g ms' ∧
      ∃ x ∈ preKeyRepresentations compI0 r S g ms' Census443Defs.torsionWireBytes,
        ¬ BobStartCollision compI0 r S g ms' p x := by
  have hp' := hp
  rw [census_torsionWireBytes] at hp'
  rcases hfits.1 with ⟨hwf, -, -, -, -, -, -, hb, hs, -, -, -, -, hEq, -, -⟩
  have hs1 : compSecretIdx (clamp (secretBytes r 1)) = some ⟨4, by decide⟩ := by rw [hb]; exact torsionComp_compSecretIdx_bobId
  have hs2 : compSecretIdx (clamp (secretBytes r 2)) = some ⟨3, by decide⟩ := by rw [hs]; exact torsionComp_compSecretIdx_spk
  obtain ⟨q₀, hq₀, -⟩ := sentWireBytes_innerWireCanonical.1
  have hcan : InnerWireCanonical p := torsionWireBytes_innerWireCanonical.2 p hp'
  obtain ⟨hpbk, hkc, hpm, -, -⟩ := wirePairOk_spec wirePairOk_torsion hq₀ hp'
  have hv0 : variantBytes compEkATorsion 0 = compEkATorsion := by decide +kernel
  obtain ⟨pre, mid, post, hb_eq, shown, cl, e, c', hms_eq, hc, hmr, hvis, hpre, hmid, hpost, hm₀, hnil, hex', hx₀⟩ :=
    split38_decomp_swap_rep_cli (v := 0) (t := 1) hwf.1 hnb hEq hs1 hs2 hcs rfl rsT_len rsT_kind bunBytes_getElem4_ne sentWireBytes_head_ne sentWireBytes_hasTag4 sentWireBytes_len hq₀ (sentWireBytes_baseKey hq₀)
      (fun _ => by rw [sentWireBytes_kyberCiphertext hq₀, compI0_kyberEncaps_rsT])
      hp'
      (fun k hk hγ => by
        rw [gamma_x25519TorsionVariant' S g k 0 1 (by decide), hk, hγ, clamp_b0_lookup, torsionShift_compEkAPub_one, hv0]
        exact hpbk)
      hkc hpm hcan (outer_torsion hfits.1 hp') (CompRX0Split38.attackerKnows_torsionVariant 0 1) hex
  rw [← census_torsionWireBytes] at hx₀
  have hnbsc := nbscTorsionComp_split hcs compI0 r S hfits g p hp
  unfold Census443Defs.NBSC38' at hnbsc
  rw [census_iniAliceOut, census_iniAliceStartState, census_iniAliceStartTr, census_encOut] at hnbsc
  obtain ⟨hnb_pre, hnb_mid, hnb_post⟩ := CompRX0Top.noBrkTr_split38 (hms_eq ▸ hnb)
  exact ⟨pre, mid, post, hb_eq, shown, cl, e, c', hms_eq, hpre, hmid, hpost, hm₀, hex', _, hx₀,
    hnbsc pre mid post hb_eq shown cl e c' hc hmr hvis (CompRX0SS38.movesFrom_to_census443 hnb_pre hpre) (CompRX0SS38.movesFrom_to_census443 hnb_mid hmid) (CompRX0SS38.movesFrom_to_census443 hnb_post hpost) hm₀ hnil⟩

theorem noBsc38TC_cli {who : List Participant} {ok : Nat → Bool} {σ₁ blk₁ : List MachineEvent}
    (hcs : Cli.CoinSplit [.pt CompRX0SS38.ptB, .rng CompRX0SS38.cB, .send CompRPlantWire.sentWireBytes] blk₁)
    (r : Records) (S : Sem) (g : Ghost) (ms : List Move) (p : PreKeyFields)
    (hfits : compFitsPinned Symbolic.BugInjection.Witnesses.Cheval26SmallSubgroupTorsionComp.setup compI0 r)
    (hnb : CompSetupSecrecy.NoBrk r ms)
    (hex : ExplainsCli compI0 r S who ok σ₁
      ((.recv CompRX0SS38.bunBytes :: .rng CompRX0SS38.b0Bytes :: CompRX0SS38.rsT) ++ blk₁) g ms)
    (hp : parsePreKeyWire Census443Defs.torsionWireBytes = some p) :
    ∃ g' ms', ExplainsCli compI0 r S who ok σ₁
        ((.recv CompRX0SS38.bunBytes :: .rng CompRX0SS38.b0Bytes :: CompRX0SS38.rsT) ++ blk₁) g' ms' ∧
      ∃ x ∈ preKeyRepresentations compI0 r S g' ms' Census443Defs.torsionWireBytes,
        ¬ BobStartCollision compI0 r S g' ms' p x := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hex', x, hx, hnbsc⟩ :=
    noBsc38TC_cli_swap hcs r S g ms p hfits hnb hex hp
  exact ⟨g, _, hex', x, hx, hnbsc⟩

abbrev cliCompFitsPinned := Symbolic.BugInjection.Proofs.Common.CompFitsSatisfiable.cliCompFitsPinned

theorem cliCompFitsPinned_imp_cliCompFits (w : PQXDHSpqrSetup)
    (iw : ExternInterpretation × CryptoVerification.SignalSession.CliHooks)
    (r : Records)
    (h : cliCompFitsPinned w iw r) : Symbolic.BugInjection.cliCompFits w iw r :=
  ⟨h.1.1, h.2.1, h.2.2⟩

theorem coinSplit_nonRng_cons {e : MachineEvent} {σ τ : List MachineEvent}
    (hne : ∀ c, e ≠ .rng c) (hcs : CoinSplit (e :: σ) τ) :
    ∃ τ', τ = e :: τ' ∧ CoinSplit σ τ' := by
  cases hcs with
  | keep _ hrest => exact ⟨_, rfl, hrest⟩
  | split => exfalso; exact hne _ rfl

theorem coinSplit_rng_cons {c : HwBytes} {σ τ : List MachineEvent}
    (hcs : CoinSplit (.rng c :: σ) τ) :
    ∃ (pieces : List HwBytes) (τ' : List MachineEvent),
      (∀ p ∈ pieces, p ≠ []) ∧ pieces.flatten <+: c ∧
      τ = pieces.map MachineEvent.rng ++ τ' ∧ CoinSplit σ τ' := by
  cases hcs with
  | keep hne _ => exact absurd rfl (hne c)
  | split hne hpref hrest => exact ⟨_, _, hne, hpref, rfl, hrest⟩

theorem map_rng_kind {pieces : List HwBytes} :
    ∀ e ∈ pieces.map MachineEvent.rng, eventKind e = .rng := by
  intro e he
  obtain ⟨_, _, rfl⟩ := List.mem_map.mp he
  rfl

theorem coinSplit_no_leak {σ τ : List MachineEvent}
    (hcs : CoinSplit σ τ) (hσ : ∀ e ∈ σ, eventKind e ≠ .leak) :
    ∀ e ∈ τ, eventKind e ≠ .leak := by
  induction hcs with
  | nil => intro _ h; nomatch h
  | keep _ _ ih =>
    intro e he
    rcases List.mem_cons.mp he with rfl | he'
    · exact hσ _ (List.mem_cons_self ..)
    · exact ih (fun x hx => hσ x (List.mem_cons_of_mem _ hx)) e he'
  | split _ _ _ ih =>
    intro e he
    rcases List.mem_append.mp he with h1 | h2
    · rw [map_rng_kind e h1]; decide
    · exact ih (fun x hx => hσ x (List.mem_cons_of_mem _ hx)) e h2

theorem coinSplit_no_accept {σ τ : List MachineEvent}
    (hcs : CoinSplit σ τ) (hσ : ∀ e ∈ σ, eventKind e ≠ .accept) :
    ∀ e ∈ τ, eventKind e ≠ .accept := by
  induction hcs with
  | nil => intro _ h; nomatch h
  | keep _ _ ih =>
    intro e he
    rcases List.mem_cons.mp he with rfl | he'
    · exact hσ _ (List.mem_cons_self ..)
    · exact ih (fun x hx => hσ x (List.mem_cons_of_mem _ hx)) e he'
  | split _ _ _ ih =>
    intro e he
    rcases List.mem_append.mp he with h1 | h2
    · rw [map_rng_kind e h1]; decide
    · exact ih (fun x hx => hσ x (List.mem_cons_of_mem _ hx)) e h2

open Symbolic.BugInjection
open Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupHighBitComp443
  (not_kyberMismatch_compI0 NoAccept not_readCollision_of_noAccept
   isAcceptedRecvKindAt isPtKindAt isAcceptedRecvKindAt_of_recv_accepted isPtKindAt_of_pt
   split_at_length not_knownBaseKey_of_bobDone_nil not_matchedPrefix_of_recv_accept_tail)

local elab "chars_of_hex_cli" id:ident : term => do
  let e := Lean.mkConst (← Lean.resolveGlobalConstNoOverload id)
  let eWhnf ← Lean.Meta.whnf e
  let args := eWhnf.getAppArgs
  let sLit ← Lean.Meta.whnf args[0]!
  match sLit with
  | .lit (.strVal s) => return Lean.toExpr s.toList
  | _ => throwError "not strVal: {sLit}"

local elab "str_of_hex_cli" id:ident : term => do
  let e := Lean.mkConst (← Lean.resolveGlobalConstNoOverload id)
  let eWhnf ← Lean.Meta.whnf e
  let args := eWhnf.getAppArgs
  let sLit ← Lean.Meta.whnf args[0]!
  return sLit

def cliCoins0 : HwBytes :=
  hexBytes "49c93ba96e848e114ccd7a9ac6fa2f998172a9bdebc69e1b8b4e2a527db2be9e051310e3058b50f2e6340ad91254ddaf320aceff3b048bcc387f996aa41a2a1f4396fa34fcba7a943f37fed8842a7a3484bd1ae79dc7fb3af4d2112dba377abdd5c50a08141ee32e1e5622a5073163413fa1c60b082178b8fc1d349d1c2f4c19060ea05c8c7ca842d116c8ba3ffdf0a7c020c1a4bc16764fdbce839c26eadab24a260419c077fbe8fa8e46b8368f6f20481ee60124cec354836099e2304f9626"

private def cliCoins0Chars : List Char := chars_of_hex_cli cliCoins0
private theorem cliCoins0_eq_hex : cliCoins0 = hexBytes (str_of_hex_cli cliCoins0) := rfl
private theorem cliCoins0Str_eq : (str_of_hex_cli cliCoins0) = String.ofList cliCoins0Chars := rfl
private def cliCoins0Fast : HwBytes := hexBytes.go CompRPlantWire.hexDigit cliCoins0Chars

private theorem cliCoins0_eq_fast : cliCoins0 = cliCoins0Fast := by
  change cliCoins0 = hexBytes.go CompRPlantWire.hexDigit cliCoins0Chars
  rw [cliCoins0_eq_hex, cliCoins0Str_eq, CompRPlantWire.hexBytes_ofList]

theorem cliCoins0_length : cliCoins0.length = 192 := by
  rw [cliCoins0_eq_fast]; rfl

private def initiateCharChunks (cs : List Char) : List (List Char) :=
  [cs.take 64] ++ (List.range 32).map (fun j => (cs.drop (64 + 8 * j)).take 8) ++ [(cs.drop 320).take 64]

private theorem map_rng_hexBytes_ofList (css : List (List Char)) :
    css.map (fun cs => MachineEvent.rng (hexBytes (String.ofList cs))) =
    css.map (fun cs => MachineEvent.rng (hexBytes.go CompRPlantWire.hexDigit cs)) := by
  induction css with
  | nil => rfl
  | cons cs css ih =>
    simp only [List.map_cons, CompRPlantWire.hexBytes_ofList]

private theorem call0RngEvents_eq_ofList :
    Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupHighBitComp443.call0RngEvents =
      (initiateCharChunks cliCoins0Chars).map (fun cs => MachineEvent.rng (hexBytes (String.ofList cs))) := rfl

private theorem call0RngEvents_eq_b0_rsT :
    Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupHighBitComp443.call0RngEvents =
      MachineEvent.rng CompRX0SS38.b0Bytes :: CompRX0SS38.rsT := by
  rw [CompRX0SS38.b0Bytes_eq_hex]
  rfl

theorem initiateDrawsOfCoins_cliCoins0_eq :
    (CliCoinSplit.initiateDrawsOfCoins cliCoins0).map MachineEvent.rng =
      MachineEvent.rng CompRX0SS38.b0Bytes :: CompRX0SS38.rsT := by
  rw [← call0RngEvents_eq_b0_rsT, cliCoins0_eq_fast, call0RngEvents_eq_ofList, map_rng_hexBytes_ofList]
  rfl

theorem init_draws_cliCoins0_eq_hb :
    .recv CompRX0SS38.bunBytes :: (CliCoinSplit.initiateDrawsOfCoins cliCoins0).map MachineEvent.rng =
      Symbolic.BugInjection.Witnesses.Cheval26SmallSubgroupHighBitComp.trace.take 35 := by
  rw [initiateDrawsOfCoins_cliCoins0_eq, ← call0RngEvents_eq_b0_rsT, CompRX0SS38.bunBytes_eq_hex]
  rfl

theorem init_draws_cliCoins0_eq_tc :
    .recv CompRX0SS38.bunBytes :: (CliCoinSplit.initiateDrawsOfCoins cliCoins0).map MachineEvent.rng =
      Symbolic.BugInjection.Witnesses.Cheval26SmallSubgroupTorsionComp.trace.take 35 := by
  rw [initiateDrawsOfCoins_cliCoins0_eq, ← call0RngEvents_eq_b0_rsT, CompRX0SS38.bunBytes_eq_hex]
  rfl

theorem no_coinSplit_matchedPrefix_of_gen
    (σ_pre : List MachineEvent) (wire rng39 acc40 : HwBytes)
    (hpre_noleak : ∀ e ∈ σ_pre, eventKind e ≠ .leak)
    (hhead_ne : wire.head? ≠ some DY.Libsignal.TripleRatchet.Refinement.wireWhisperTag)
    (hq_some : (parsePreKeyWire wire).isSome = true)
    (hbase_ne : ∀ o : Option (Fin 12),
      (parsePreKeyWire wire).map (fun p => p.baseKey.take 33) ≠ some (ecKey (compPubOfOpt o)))
    {r : Records} {S : Sem} {who₀ : List Participant} {τhw : List MachineEvent}
    {g : Ghost} {ms : List Move}
    (hnb : CompSetupSecrecy.NoBrk r ms)
    (hcs : CoinSplit (σ_pre ++ [.recv wire, .rng rng39, .accept acc40]) τhw) :
    ¬ DY.Libsignal.Composed.Refinement.MatchedPrefix compI0 r S who₀ g ms τhw := by
  intro hmp
  obtain ⟨τ₁, τ₂, rfl, hcs₁, hcs₂⟩ := CliCoinSplit.coinSplit_append_inv hcs
  obtain ⟨τ₂', rfl, hcs₂'⟩ := coinSplit_nonRng_cons (fun _ h => by cases h) hcs₂
  obtain ⟨pieces, τ₂'', _, _, rfl, hcs₂''⟩ := coinSplit_rng_cons hcs₂'
  obtain ⟨τ₂''', rfl, hcs₂'''⟩ := coinSplit_nonRng_cons (fun _ h => by cases h) hcs₂''
  cases hcs₂'''
  have hnoleak : ∀ e ∈ τ₁ ++ (MachineEvent.recv wire :: (pieces.map MachineEvent.rng ++ [MachineEvent.accept acc40])),
      eventKind e ≠ .leak := by
    apply coinSplit_no_leak hcs
    intro e he
    rcases List.mem_append.mp he with h1 | h2
    · exact hpre_noleak e h1
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h2
      rcases h2 with rfl | rfl | rfl <;> { dsimp [eventKind]; decide }
  have hrest_ne : ∀ e ∈ pieces.map MachineEvent.rng ++ [MachineEvent.accept acc40],
      eventKind e ≠ .recv ∧ eventKind e ≠ .pt ∧ eventKind e ≠ .leak := by
    intro e he
    rcases List.mem_append.mp he with h1 | h2
    · rw [map_rng_kind e h1]; decide
    · simp only [List.mem_singleton] at h2; subst h2; dsimp [eventKind]; decide
  have hacc : ∃ e ∈ pieces.map MachineEvent.rng ++ [MachineEvent.accept acc40],
      eventKind e = .accept :=
    ⟨.accept acc40, List.mem_append_right _ (List.mem_singleton_self _), rfl⟩
  exact not_matchedPrefix_of_recv_accept_tail rfl
    (Symbolic.Swarm.CREF.MatchedPrefix.of_composed hmp)
    hnb hnoleak hrest_ne hacc hhead_ne hq_some hbase_ne

end Symbolic.BugInjection.Proofs.Common443.CliCoinSplitClose
