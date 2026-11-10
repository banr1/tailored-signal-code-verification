/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.CompRX0Join
public import Symbolic.BugInjection.Proofs.Common443.CompRX0Decomp
public import Symbolic.BugInjection.Proofs.Common443.CompRX0Bytes
public import Symbolic.BugInjection.Proofs.Common443.CompRX0Gamma
public import Symbolic.BugInjection.Proofs.Common443.CompPrefixInvBundle

@[expose] public section
set_option autoImplicit false
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Common443.CompRX0Top
open DY
open DY.Libsignal (HwBytes)
open DY.Libsignal.Composed DY.Libsignal.Composed.Refinement DY.Libsignal.HwEvents Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Proofs.Common443 Symbolic.BugInjection.Proofs.Common443.CompPrefixInvEnc Symbolic.BugInjection.Proofs.Common443.CompPrefixInvBundle Symbolic.BugInjection.Proofs.Common443.CompPrefixInvStruct Symbolic.BugInjection.Proofs.Common443.CompRFaithfulInner Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompTrace
open CryptoProofLib.Refinement (ExternInterpretation)
open Symbolic.BugInjection.Proofs.Common443.CompRX0Gamma (coinHeads)
open Symbolic.BugInjection.Proofs.Common443.CompRX0Mem (sendMatches_append_inv)
open DY.Libsignal.PQXDH.Refinement (kyberEncapsSymbol)
def NoBrkTr (tr : ExecTrace) : Prop :=
  ∀ j (e : PQXDHEntry), (tr.at? j : Option PQXDHEntry) = some e →
    Symbolic.Proofs.Swarm.CREF.Cli.MoveBrkLemmas.isBreakPQEv e.ev = false
theorem noBrkTr_of_le {tr₁ tr₂ : ExecTrace} (hle : tr₁ ≤ tr₂) (h : NoBrkTr tr₂) : NoBrkTr tr₁ := by
  intro j e hj
  rw [← CompSetupSecrecy.at?_eq_of_le_of_lt hle (Symbolic.Swarm.CREF.XplSteps.xlt_of_at?_some hj)] at hj
  exact h j e hj
theorem noBrkTr_of_noBrk {r : Records} {ms : List Move} (h : CompSetupSecrecy.NoBrk r ms) :
    NoBrkTr (runTraceMoves r ms) := by
  intro j ⟨ev⟩ hj
  cases ev with
  | BrokenDH =>
    exact absurd ⟨j, (Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.eventLoggedAt_iff_at?
      DY.Libsignal.PQXDH.PQXDHEvent _ _ _).mpr hj⟩ h.1
  | BrokenKEM =>
    exact absurd ⟨j, (Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.eventLoggedAt_iff_at?
      DY.Libsignal.PQXDH.PQXDHEvent _ _ _).mpr hj⟩ h.2
  | _ => rfl
theorem noBrkTr_split38 {r : Records} {pre mid post : List Move} {m₀ m₁ : Move}
    (hnb : CompSetupSecrecy.NoBrk r (pre ++ m₀ :: mid ++ m₁ :: post)) :
    let tr₁ := (runMoves pre (setupTrace r)).1
    let tr₂ := (runMoves mid (m₀.next tr₁)).1
    NoBrkTr tr₁ ∧ NoBrkTr tr₂ ∧ NoBrkTr (runMoves post (m₁.next tr₂)).1 := by
  dsimp only
  let tr₁ := (runMoves pre (setupTrace r)).1
  let tr₂ := (runMoves mid (m₀.next tr₁)).1
  have htr : runTraceMoves r (pre ++ m₀ :: mid ++ m₁ :: post) =
      (runMoves post (m₁.next tr₂)).1 := by
    rw [Symbolic.Swarm.CREF.xpl_runTrace_eq, List.append_assoc,
      CompPrefixInvStruct.runMoves_append_fst]
    change (runMoves (mid ++ m₁ :: post) (m₀.next tr₁)).1 = _
    rw [CompPrefixInvStruct.runMoves_append_fst]
    rfl
  have hpost : NoBrkTr (runMoves post (m₁.next tr₂)).1 := htr ▸ noBrkTr_of_noBrk hnb
  have hmid : NoBrkTr tr₂ :=
    noBrkTr_of_le (Trace.le_trans _ _ _ (Move.le_next m₁ tr₂) (CompPrefixInvEnc.runMoves_le post _)) hpost
  have hpre : NoBrkTr tr₁ :=
    noBrkTr_of_le (Trace.le_trans _ _ _ (Move.le_next m₀ tr₁) (CompPrefixInvEnc.runMoves_le mid _)) hmid
  exact ⟨hpre, hmid, hpost⟩
theorem noBrk_append_left {r : Records} {ms₁ ms₂ : List Move}
    (hnb : CompSetupSecrecy.NoBrk r (ms₁ ++ ms₂)) : CompSetupSecrecy.NoBrk r ms₁ :=
  CompSetupSecrecy.noBrk_of_le (by
    rw [Symbolic.Swarm.CREF.xpl_runTrace_eq (ms := ms₁ ++ ms₂),
      CompPrefixInvStruct.runMoves_append_fst (ms₁ := ms₁),
      ← Symbolic.Swarm.CREF.xpl_runTrace_eq]
    exact CompPrefixInvEnc.runMoves_le _ _) hnb
theorem noBrk_take {r : Records} {ms : List Move}
    (hnb : CompSetupSecrecy.NoBrk r ms) (k : Nat) : CompSetupSecrecy.NoBrk r (ms.take k) :=
  noBrk_append_left (ms₂ := ms.drop k) (by rw [List.take_append_drop]; exact hnb)
theorem split38_decomp_swap_rep_top {r : Records} {S : Sem} {who : List Participant} {ok : Nat → Bool} {g : Ghost} {ms : List Move} {τ₁ : List MachineEvent} {bun b₀ pt c w b : HwBytes} {rs' : List MachineEvent} {p q₀ : PreKeyFields} (v : Fin 4) (t : Fin 8) (hNe : r.alice ≠ r.bob) (hnb : CompSetupSecrecy.NoBrk r ms) (hEq : DY.Libsignal.Refinement.CryptoEquationsHold compI0) (hs1 : compSecretIdx (clamp (secretBytes r 1)) = some ⟨4, by decide⟩) (hs2 : compSecretIdx (clamp (secretBytes r 2)) = some ⟨3, by decide⟩) (hτ₁ : τ₁ = (.recv bun :: .rng b₀ :: rs') ++ [.pt pt, .rng c, .send w]) (hrs_len : rs'.length = 33) (hrs_kind : ∀ e ∈ (MachineEvent.rng b₀ :: rs'), eventKind e = .rng) (hbun4 : bun[4]? ≠ some 1#8) (hw : w.head? ≠ some DY.Libsignal.TripleRatchet.Refinement.wireWhisperTag) (hw4 : CompRBobInit.hasTag4 w = false) (hlen : w.length < 2 ^ 63) (hq₀ : parsePreKeyWire w = some q₀) (hbk₀ : q₀.baseKey = ecKey (compLookupPub (clamp b₀))) (hkc₀ : Compat compI0 r S g → q₀.kyberCiphertext = some (kyberKey (((compI0 kyberEncapsSymbol [gamma compI0 S g (setupPublic r 6), coinHeads (rs'.take 32)]).getD []).take 1568))) (hp : parsePreKeyWire b = some p) (hbk : ∀ k : DY.Bytes, DY.X25519.x25519Key k = k → gamma compI0 S g k = compLookupPub (clamp b₀) → p.baseKey.take 33 = ecKey (gamma compI0 S g (DY.X25519.x25519TorsionVariant k v t))) (hkc : p.kyberCiphertext = q₀.kyberCiphertext) (hpm : p.message = q₀.message) (hcan : InnerWireCanonical p) (hout : CompRPreKeyWire.PreKeyOuterMatches compI0 r b p) (hkvar : ∀ (tr : ExecTrace) (k : DY.Bytes), DY.X25519.x25519Key k = k → k.AttackerKnows tr → (DY.X25519.x25519TorsionVariant k v t).AttackerKnows tr) (hex : ExplainsMoves compI0 r S who ok g ms τ₁) : ∃ (pre mid post : List Move) (hb : DY.Libsignal.PQXDH.BundleHandles) (shown cl e c' : Nat), let tr₁ := (runMoves pre (setupTrace r)).1;
      let o := aliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none; let m₀ := Move.aliceStart r.alice r.bob 4 6 hb shown; let tr₂ := (runMoves mid (m₀.next tr₁)).1; let stA := aliceStartState tr₁ r.bob o; let ms₀ := pre ++ m₀ :: mid ++ .encrypt r.alice (tr₁.length + 8) cl (tr₂.length + 2) (some (e, c')) :: post;
      let ms' := pre ++ m₀ :: mid ++ .encrypt r.alice (tr₁.length + 8) cl (tr₂.length + 2)
          (some (tr₁.length + 3, tr₁.length + 4)) :: post;
      let x₀ : PreKeyRep := ⟨DY.X25519.x25519TorsionVariant o.ek v t, o.ct, encOut tr₂ stA cl (tr₂.length + 2)⟩;
      ms = ms₀ ∧ Compat compI0 r S g ∧ ModelRun r ms₀ ∧ List.Forall₂ (EventMatchesEntry compI0 r S g) τ₁ (runVis r ms₀) ∧ MovesFrom InvisibleNoEffect (setupTrace r) pre ∧
      MovesFrom InvisibleNoEffect (m₀.next tr₁) mid ∧
      MovesFrom InvisibleNoEffect
        ((Move.encrypt r.alice (tr₁.length + 8) cl (tr₂.length + 2) (some (e, c'))).next tr₂) post ∧
      m₀.next tr₁ = aliceStartTrOfOut tr₁ r.alice r.bob o ∧
      bobDoneBaseKeys (runTraceMoves r ms₀) = [] ∧ ExplainsMoves compI0 r S who ok g ms' τ₁ ∧
      x₀ ∈ preKeyRepresentations compI0 r S g ms' b := by
  have hmp : DY.Libsignal.Composed.Refinement.MatchedPrefix compI0 r S who g ms
      ((.recv bun :: .rng b₀ :: rs') ++ [.pt pt, .rng c, .send w]) := hτ₁ ▸ hex.1
  obtain ⟨pre, a, idS, hb, shown, mid, cl, e, c', post, ikA, tr₁, tr₂, o, stA, htr₁, ho, hstA, htr₂, hms, hdisj, hek, hct, hekK, hctK, hencK, hnil, hvis₀, hsm, hm₀, hpre, hmid, hpost⟩ :=
    CompRX0Decomp.pia_x0_decomp hNe hnb hmp (by simp [hrs_len]) hrs_kind hbun4 hw
  have hc : Compat compI0 r S g := hex.1.1; have hmr : ModelRun r ms := hex.1.2.1; have hvis : List.Forall₂ (EventMatchesEntry compI0 r S g) τ₁ (runVis r ms) := hex.1.2.2.2.2.2
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
      (hbk _ (Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.x25519Key_dhPk_eq _) hek_γ) hkc hpm hcan hout hex (hkvar _ _ (Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.x25519Key_dhPk_eq _) hekK) hctK hencK
    exact ⟨pre, mid, post, hb, shown, cl, e, c', rfl, hc, hmr, hvis, hpre, hmid, hpost, hm₀, hnil, hex', hmem'⟩
  · exfalso; subst hidS ha hikA ho hstA; obtain ⟨ek', ct', hL, -⟩ := sendMatches_append_inv hsm hlen hq₀; rw [hL] at hsm; exact CompRX0Bytes.not_sendMatches_bobSelf hNe hEq hc hs1 hs2 w hw4 tr₁ tr₂ r.bob _ _ ek' ct' cl _ hsm
end Symbolic.BugInjection.Proofs.Common443.CompRX0Top
